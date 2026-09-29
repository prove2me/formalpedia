-- Prove2me | Theorems.Thm_ConeLifts_Factorization_factorization_theorem
-- name    : ConeLifts.Factorization.factorization_theorem
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T13:47:50.283949+00:00
-- url     : https://prove2.me/theorems/1ab92087-157a-4873-a422-18f34474e144
-- title:
--   Theorem 2.4 — a proper $K$-lift gives a $K$-factorization of $S_C$, and a $K$-factorization gives a $K$-lift
-- statement:
--   Let $K \subseteq \mathbb R^m$ be a full-dimensional closed convex cone and $C \subseteq \mathbb R^n$, $n \ge 1$, a convex body (compact, convex, $0 \in \operatorname{int} C$). Let $S_C(x,y) = 1 - \langle x, y\rangle$ on $\operatorname{ext}(C) \times \operatorname{ext}(C^\circ)$ be the slack operator of $C$. Then:
--
--   1. if $C$ has a proper $K$-lift, that is $C = \pi(K \cap L)$ for an affine subspace $L$ meeting $\operatorname{int} K$ and a linear map $\pi$, then $S_C$ is $K$-factorizable;
--   2. conversely, if $S_C$ is $K$-factorizable, that is, for some maps $A : \operatorname{ext}(C) \to K$ and $B : \operatorname{ext}(C^\circ) \to K^*$
--   $$
--   1 - \langle x, y\rangle = \langle A(x), B(y)\rangle \quad \text{for all } (x,y)\in \operatorname{ext}(C)\times\operatorname{ext}(C^\circ),
--   $$
--   then $C$ has a $K$-lift (not necessarily proper).
--
--   This is the paper's central correspondence between the geometry of lifts and the algebra of cone factorizations. It extends Yannakakis' theorem, which relates polyhedral lifts of a polytope to nonnegative factorizations of its slack matrix, to arbitrary closed convex cones, in particular to positive semidefinite lifts.
--
--   **Formalization Note** The two halves are a conjunction of implications, not an equivalence: properness is assumed only in the first, and the lift produced by the second may be improper. $n \ge 1$ is the paper's implicit full-dimensionality of $C$; for $n = 0$ the first half is false ($C = \{0\}$, $K = \mathbb R^m$, $K^* = \{0\}$). $\mathbb R^k$ is `EuclideanSpace ℝ (Fin k)`, the polar is one-sided, and $A, B$ are total functions constrained on the extreme points only.
-- source:
--   Gouveia, Parrilo & Thomas, Lifts of Convex Sets and Cone Factorizations, arXiv:1111.3164v2, p. 4, Theorem 2.4

import Mathlib
import Definitions.Def_ConeLifts_Factorization_IsConvexBody
import Definitions.Def_ConeLifts_Factorization_IsClosedConvexCone
import Definitions.Def_ConeLifts_Factorization_HasLift
import Definitions.Def_ConeLifts_Factorization_HasProperLift
import Definitions.Def_ConeLifts_Factorization_SlackFactorizable

namespace ConeLifts.Factorization

/-- **Theorem 2.4** of Gouveia, Parrilo & Thomas, *Lifts of Convex Sets and Cone Factorizations*,
arXiv:1111.3164v2, p. 4: "If C has a proper K-lift then S_C is K-factorizable. Conversely, if S_C
is K-factorizable then C has a K-lift."

Standing hypotheses (Definition 2.1, p. 3): `K ⊆ ℝᵐ` is a full-dimensional closed convex cone and
`C ⊆ ℝⁿ` is a convex body (compact, convex, `0 ∈ int C`). `1 ≤ n` is the paper's implicit
"full-dimensional convex body in ℝⁿ": for `n = 0` the first half is false. The converse
concludes a `K`-lift that need not be proper. -/
theorem factorization_theorem {n m : ℕ} (hn : 1 ≤ n)
    (C : Set (EuclideanSpace ℝ (Fin n))) (hC : IsConvexBody C)
    (K : Set (EuclideanSpace ℝ (Fin m))) (hK : IsClosedConvexCone K)
    (hKint : (interior K).Nonempty) :
    (HasProperLift K C → SlackFactorizable K C) ∧ (SlackFactorizable K C → HasLift K C) := by sorry

end ConeLifts.Factorization
