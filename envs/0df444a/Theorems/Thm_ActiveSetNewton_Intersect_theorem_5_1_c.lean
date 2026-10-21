-- Prove2me | Theorems.Thm_ActiveSetNewton_Intersect_theorem_5_1_c
-- name    : ActiveSetNewton.Intersect.theorem_5_1_c
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:11:06.513714+00:00
-- url     : https://prove2.me/theorems/da24610b-95c2-4edc-938a-773ad03c75bb
-- title:
--   Theorem 5.1(c), p. 10 — a Lipschitz right inverse Q : M ∩ W → X of P fixing z exists, and near z the fiber projection Proj_{P⁻¹(w)}(w) is one
-- statement:
--   Under the hypotheses of Theorem 5.1 — $z$ an isolated, transversal point of intersection of two $C^{(2)}$-manifolds $\mathcal X$, $\mathcal Y$ around $z$ in a Euclidean space $\mathbf E$, and $P$ a map of $\mathcal X$ into $\mathcal Y$ fixing $z$ that is $C^{(2)}$-smooth and constant rank nearby — there is $r>0$ such that for every $0<\varepsilon\le r$, with $W=B(z,\varepsilon)$ and $\mathcal M=P(\mathcal X\cap W)$:
--
--   1. there is a map $Q:\mathcal M\cap W\to\mathcal X$ that is Lipschitz, fixes $z$, and is a right inverse of $P$:
--   $$P\big(Q(w)\big)=w\qquad\text{for all } w\in\mathcal M\cap W ;$$
--   2. in particular, one may take $Q(w)=\mathrm{Proj}_{P^{-1}(w)}(w)$ near $z$: for some $\delta>0$, every $w\in\mathcal M$ with $|w-z|<\delta$ has a unique nearest point in the fiber $\{x\in\mathcal X\cap W : P(x)=w\}$, and this nearest point depends Lipschitz-continuously on $w\in\mathcal M\cap B(z,\delta)$.
--
--   $Q$ is the second half of the active-set restoration: with the primal part fixed by $P$, it restores the iterate to $\mathcal X$.
--
--   **Formalization Note** The "in particular" clause is stated on a ball $B(z,\delta)$ around $z$ rather than on all of $\mathcal M\cap W$, because the paper's proof shows the fiber projection exists and is $C^{(1)}$ only for $w$ near $z$. The fiber is taken inside $\mathcal X\cap W$, as in the proof's compact neighborhood $\hat{\mathcal X}$ (p. 11); a point of the fiber is in $\mathcal X$, hence the right-inverse property $P(Q(w))=w$ is built into the nearest-point condition. Small $W$ means open balls $B(z,\varepsilon)$, $0<\varepsilon\le r$.
-- source:
--   Lewis & Wylie, Active-set Newton methods and partial smoothness, arXiv:1902.00724v1, p. 10, Theorem 5.1(c); proof pp. 10–11

import Mathlib
import Definitions.Def_ProjLikeRetr_Retractor_tangentBundle
import Definitions.Def_ActiveSetNewton_Intersect_Basic

namespace ActiveSetNewton.Intersect

open Metric

/-- Theorem 5.1(c), p. 10: for every sufficiently small ball `W = B(z, ε)`, with
`M = P(X ∩ W)`, there is a Lipschitz right inverse `Q : M ∩ W → X` of `P` fixing `z`; and near
`z` the fiber projection `Q(w) = Proj_{P⁻¹(w)}(w)` (fiber taken in `X ∩ W`) is such a map. -/
theorem theorem_5_1_c {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {X Y : Set E} {z : E} {P : E → E}
    (hX : IsCManifoldAround 2 X z) (hY : IsCManifoldAround 2 Y z)
    (hiso : IsolatedIntersection X Y z) (htr : TransversalAt X Y z)
    (hPXY : Set.MapsTo P X Y) (hPz : P z = z) (hP : HasConstantRankNear P X z) :
    ∃ r > 0, ∀ ε, 0 < ε → ε ≤ r →
      (∃ Q : E → E, Set.MapsTo Q (P '' (X ∩ ball z ε) ∩ ball z ε) X ∧
          (∃ K, LipschitzOnWith K Q (P '' (X ∩ ball z ε) ∩ ball z ε)) ∧ Q z = z ∧
          ∀ w ∈ P '' (X ∩ ball z ε) ∩ ball z ε, P (Q w) = w) ∧
      (∃ δ > 0, ∃ Q : E → E,
          (∀ w ∈ P '' (X ∩ ball z ε) ∩ ball z δ,
            IsNearestPoint (X ∩ ball z ε ∩ P ⁻¹' {w}) w (Q w)) ∧
          ∃ K, LipschitzOnWith K Q (P '' (X ∩ ball z ε) ∩ ball z δ)) := by sorry

end ActiveSetNewton.Intersect
