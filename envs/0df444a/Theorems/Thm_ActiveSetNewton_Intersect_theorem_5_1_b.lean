-- Prove2me | Theorems.Thm_ActiveSetNewton_Intersect_theorem_5_1_b
-- name    : ActiveSetNewton.Intersect.theorem_5_1_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:11:01.39212+00:00
-- url     : https://prove2.me/theorems/1cffe42d-8aff-4f84-a92e-2e052d673fc1
-- title:
--   Theorem 5.1(b), p. 10 — a Lipschitz S : Y ∩ W → M fixing z exists, and near z the projection Proj_M is single-valued and Lipschitz
-- statement:
--   Under the hypotheses of Theorem 5.1 — $z$ an isolated, transversal point of intersection of two $C^{(2)}$-manifolds $\mathcal X$, $\mathcal Y$ around $z$ in a Euclidean space $\mathbf E$, and $P$ a map of $\mathcal X$ into $\mathcal Y$ fixing $z$ that is $C^{(2)}$-smooth and constant rank nearby — there is $r>0$ such that for every $0<\varepsilon\le r$, with $W=B(z,\varepsilon)$ and $\mathcal M=P(\mathcal X\cap W)$:
--
--   1. there is a map $S:\mathcal Y\cap W\to\mathcal M$ that is Lipschitz and fixes $z$;
--   2. in particular, the nearest-point projection is such a map near $z$: for some $\delta>0$ every $y\in\mathcal Y$ with $|y-z|<\delta$ has a unique nearest point $\mathrm{Proj}_{\mathcal M}(y)$ in $\mathcal M$, and
--   $$y\;\mapsto\;\mathrm{Proj}_{\mathcal M}(y)\quad\text{is Lipschitz on } \mathcal Y\cap B(z,\delta).$$
--
--   The projection $\mathrm{Proj}_{\mathcal M}$ is the first half of the active-set restoration: it identifies the active manifold in the primal space.
--
--   **Formalization Note** The first clause alone is witnessed by the constant map $S\equiv z$; the content is the second. The paper writes $\mathrm{Proj}_{\mathcal M}:\mathcal Y\cap W\to\mathcal M$ on all of $\mathcal Y\cap W$; since $\mathcal M$ is not closed, a point of $\mathcal Y\cap W$ near the boundary of $W$ may have no nearest point in $\mathcal M$, and the paper's argument (smoothness of the projection onto a $C^{(2)}$-manifold around $z$) gives it only around $z$. The clause is therefore stated on a ball $B(z,\delta)$ for some $\delta>0$. Small $W$ means open balls $B(z,\varepsilon)$, $0<\varepsilon\le r$.
-- source:
--   Lewis & Wylie, Active-set Newton methods and partial smoothness, arXiv:1902.00724v1, p. 10, Theorem 5.1(b)

import Mathlib
import Definitions.Def_ProjLikeRetr_Retractor_tangentBundle
import Definitions.Def_ActiveSetNewton_Intersect_Basic

namespace ActiveSetNewton.Intersect

open Metric

/-- Theorem 5.1(b), p. 10: for every sufficiently small ball `W = B(z, ε)`, with
`M = P(X ∩ W)`, there is a map `S : Y ∩ W → M` that is Lipschitz and fixes `z`; and near `z`
the nearest-point projection `Proj_M` is such a map (it is single-valued and Lipschitz on
`Y ∩ B(z, δ)` for some `δ > 0`). -/
theorem theorem_5_1_b {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {X Y : Set E} {z : E} {P : E → E}
    (hX : IsCManifoldAround 2 X z) (hY : IsCManifoldAround 2 Y z)
    (hiso : IsolatedIntersection X Y z) (htr : TransversalAt X Y z)
    (hPXY : Set.MapsTo P X Y) (hPz : P z = z) (hP : HasConstantRankNear P X z) :
    ∃ r > 0, ∀ ε, 0 < ε → ε ≤ r →
      (∃ S : E → E, Set.MapsTo S (Y ∩ ball z ε) (P '' (X ∩ ball z ε)) ∧
          (∃ K, LipschitzOnWith K S (Y ∩ ball z ε)) ∧ S z = z) ∧
      (∃ δ > 0, ∃ S : E → E,
          (∀ y ∈ Y ∩ ball z δ, IsNearestPoint (P '' (X ∩ ball z ε)) y (S y)) ∧
          ∃ K, LipschitzOnWith K S (Y ∩ ball z δ)) := by sorry

end ActiveSetNewton.Intersect
