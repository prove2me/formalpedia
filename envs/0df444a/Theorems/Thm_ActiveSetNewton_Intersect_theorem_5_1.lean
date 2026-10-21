-- Prove2me | Theorems.Thm_ActiveSetNewton_Intersect_theorem_5_1
-- name    : ActiveSetNewton.Intersect.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:11:07.501027+00:00
-- url     : https://prove2.me/theorems/3f51352a-f6bd-4934-8e35-d74e39d44472
-- title:
--   Theorem 5.1, pp. 9–10 — transversal C(2) manifolds with a constant-rank map P : X → Y fixing z: M = P(X ∩ W) is a manifold, Lipschitz S, Q exist, and x ← Q(S(y(x))) converges quadratically
-- statement:
--   **Theorem 5.1 (Active set method for manifold intersection).** Let $\mathbf E$ be a Euclidean space and let $z$ be an isolated point of intersection of two $C^{(2)}$-manifolds $\mathcal X$ and $\mathcal Y$ around $z$, intersecting transversally: $N_{\mathcal X}(z)\cap N_{\mathcal Y}(z)=\{0\}$. Let $P$ map $\mathcal X$ into $\mathcal Y$, fix $z$, and be $C^{(2)}$-smooth and constant rank nearby. Then there is $r>0$ such that for every $0<\varepsilon\le r$, with $W=B(z,\varepsilon)$ and $\mathcal M=P(\mathcal X\cap W)$:
--
--   1. **(a)** $\mathcal M$ is a $C^{(2)}$-manifold around $z$;
--   2. **(b)** there is a Lipschitz map $S:\mathcal Y\cap W\to\mathcal M$ fixing $z$; in particular, for some $\delta>0$ the projection $\mathrm{Proj}_{\mathcal M}$ is single-valued and Lipschitz on $\mathcal Y\cap B(z,\delta)$;
--   3. **(c)** there is a Lipschitz map $Q:\mathcal M\cap W\to\mathcal X$ fixing $z$ with $P(Q(w))=w$ for all $w\in\mathcal M\cap W$; in particular, for some $\delta>0$ the fiber projection $w\mapsto\mathrm{Proj}_{P^{-1}(w)}(w)$ (fiber within $\mathcal X\cap W$) is single-valued and Lipschitz on $\mathcal M\cap B(z,\delta)$;
--   4. **(d)** for every $x\in\mathcal X\cap W$ the linear approximation $x+T_{\mathcal X}(x)$ meets $\mathcal Y\cap W$ in exactly one point $y(x)$;
--   5. for **every** $S$ and $Q$ as in (b) and (c) (Lipschitz, fixing $z$, $S$ mapping $\mathcal Y\cap W$ into $\mathcal M$, $Q$ mapping $\mathcal M\cap W$ into $\mathcal X$ with $P\circ Q=\mathrm{id}$ on $\mathcal M\cap W$), starting from any $x\in\mathcal X$ near $z$ the iteration
--   $$x\;\leftarrow\;Q\Big(S\big(y(x)\big)\Big)$$
--   converges quadratically to $z$.
--
--   The iteration decouples the restoration step of the semi-linearization Newton method into a primal step $S$ (identify the active manifold $\mathcal M$) and a dual step $Q$ (restore to $\mathcal X$ with the primal part fixed). In the application to generalized equations $0\in\Phi(u)$, $\mathcal X$ is the graph of $\Phi$, $\mathcal Y=\mathbf U\times\{0\}$, and the constant-rank assumption on $P(u,v)=(u,0)$ is partial smoothness of $\Phi$.
--
--   **Formalization Note**
--   1. "For any sufficiently small neighborhood $W$ of $z$" ranges over open balls $B(z,\varepsilon)$, $0<\varepsilon\le r$: for an arbitrary small open $W$ that is not star-shaped about $z$, part (d) can fail.
--   2. The two "in particular" projection clauses hold only near $z$ (the set $\mathcal M$ is not closed, and the paper's proof gives smoothness of the projections around $z$), so they are stated on a ball $B(z,\delta)$ for some $\delta>0$.
--   3. "$C^{(2)}$-smooth and constant rank nearby" means $C^{(2)}$ on an open set of $\mathbf E$ around $z$, with the rank of $DP(x)$ on $T_{\mathcal X}(x)$ constant for $x\in\mathcal X$ near $z$.
--   4. The convergence claim is stated for every admissible $S$, $Q$ and for the point $y(x)$ of (d); quadratic convergence means one constant $C$ for all starting points within some $\delta$ of $z$, iterates staying in $\mathcal X$ within $\delta$ of $z$, $|x_{n+1}-z|\le C|x_n-z|^2$, and convergence to $z$. Maps are total functions on $\mathbf E$; every Lipschitz and mapping condition is imposed only on the paper's domain.
-- source:
--   Lewis & Wylie, Active-set Newton methods and partial smoothness, arXiv:1902.00724v1, pp. 9–10, Theorem 5.1

import Mathlib
import Definitions.Def_ProjLikeRetr_Retractor_tangentBundle
import Definitions.Def_ActiveSetNewton_Intersect_Basic

namespace ActiveSetNewton.Intersect

open Metric

/-- Theorem 5.1 (Active set method for manifold intersection), pp. 9–10: parts (a)–(d) for every
sufficiently small ball `W = B(z, ε)` and `M = P(X ∩ W)`, and quadratic convergence of
`x ← Q(S(y(x)))` for every admissible `S`, `Q` and the semi-linearization point `y(x)` of (d). -/
theorem theorem_5_1 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {X Y : Set E} {z : E} {P : E → E}
    (hX : IsCManifoldAround 2 X z) (hY : IsCManifoldAround 2 Y z)
    (hiso : IsolatedIntersection X Y z) (htr : TransversalAt X Y z)
    (hPXY : Set.MapsTo P X Y) (hPz : P z = z) (hP : HasConstantRankNear P X z) :
    ∃ r > 0, ∀ ε, 0 < ε → ε ≤ r →
      -- (a)
      IsCManifoldAround 2 (P '' (X ∩ ball z ε)) z ∧
      -- (b)
      (∃ S : E → E, Set.MapsTo S (Y ∩ ball z ε) (P '' (X ∩ ball z ε)) ∧
          (∃ K, LipschitzOnWith K S (Y ∩ ball z ε)) ∧ S z = z) ∧
      -- (b), in particular: Proj_M, near z
      (∃ δ > 0, ∃ S : E → E,
          (∀ y ∈ Y ∩ ball z δ, IsNearestPoint (P '' (X ∩ ball z ε)) y (S y)) ∧
          ∃ K, LipschitzOnWith K S (Y ∩ ball z δ)) ∧
      -- (c)
      (∃ Q : E → E, Set.MapsTo Q (P '' (X ∩ ball z ε) ∩ ball z ε) X ∧
          (∃ K, LipschitzOnWith K Q (P '' (X ∩ ball z ε) ∩ ball z ε)) ∧ Q z = z ∧
          ∀ w ∈ P '' (X ∩ ball z ε) ∩ ball z ε, P (Q w) = w) ∧
      -- (c), in particular: Q(w) = Proj_{P⁻¹(w)}(w), near z
      (∃ δ > 0, ∃ Q : E → E,
          (∀ w ∈ P '' (X ∩ ball z ε) ∩ ball z δ,
            IsNearestPoint (X ∩ ball z ε ∩ P ⁻¹' {w}) w (Q w)) ∧
          ∃ K, LipschitzOnWith K Q (P '' (X ∩ ball z ε) ∩ ball z δ)) ∧
      -- (d)
      (∀ x ∈ X ∩ ball z ε, ∃! y : E, y ∈ linApprox X x ∧ y ∈ Y ∩ ball z ε) ∧
      -- final claim: x ← Q(S(y(x))) converges quadratically, for every admissible S, Q
      (∀ S Q y : E → E,
        Set.MapsTo S (Y ∩ ball z ε) (P '' (X ∩ ball z ε)) →
        (∃ K, LipschitzOnWith K S (Y ∩ ball z ε)) → S z = z →
        Set.MapsTo Q (P '' (X ∩ ball z ε) ∩ ball z ε) X →
        (∃ K, LipschitzOnWith K Q (P '' (X ∩ ball z ε) ∩ ball z ε)) → Q z = z →
        (∀ w ∈ P '' (X ∩ ball z ε) ∩ ball z ε, P (Q w) = w) →
        (∀ x ∈ X ∩ ball z ε, y x ∈ linApprox X x ∧ y x ∈ Y ∩ ball z ε) →
        ConvergesQuadratically (fun x => Q (S (y x))) X z) := by sorry

end ActiveSetNewton.Intersect
