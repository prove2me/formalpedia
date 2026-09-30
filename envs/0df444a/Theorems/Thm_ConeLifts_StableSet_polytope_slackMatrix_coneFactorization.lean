-- Prove2me | Theorems.Thm_ConeLifts_StableSet_polytope_slackMatrix_coneFactorization
-- name    : ConeLifts.StableSet.polytope_slackMatrix_coneFactorization
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T21:18:22.181142+00:00
-- url     : https://prove2.me/theorems/8e5d574e-c4eb-459c-9f0f-accfff40105d
-- title:
--   Theorem 3.3 — a polytope with a proper $K$-lift has $K$-factorizable slack matrices
-- statement:
--   Let $n \ge 1$, let $K \subseteq \mathbb R^m$ be a full-dimensional closed convex cone and let $P \subseteq \mathbb R^n$ be a polytope (the convex hull of finitely many points) with the origin in its interior. If $P$ has a proper $K$-lift, that is, $P = \pi(K \cap L)$ for an affine subspace $L$ meeting the interior of $K$ and a linear map $\pi$, then every slack matrix $M$ of $P$ admits a $K$-factorization: there are $a^p \in K$ for the vertices $p$ of $P$ and $b^y \in K^*$ for the extreme points $y$ of $P^\circ$ with
--
--   $$
--   M_{p,y} = \langle a^p, b^y \rangle .
--   $$
--
--   This is the polytope form of the factorization theorem (Theorem 2.4). It turns the nonexistence of a lift into a statement about matrices: to rule out a proper $K$-lift it suffices to exhibit a slack matrix, or a submatrix of one, without a $K$-factorization.
--
--   **Formalization Note** "Full-dimensional closed convex cone" is the four hypotheses closed, convex, closed under nonnegative scaling, and nonempty interior. The origin in the interior of $P$ is the standing assumption of §3 and implies that $P$ is full-dimensional. "Every slack matrix" is `IsSlackMatrix`: the canonical slack matrix $(1-\langle p,y\rangle)$ on vertices of $P$ times extreme points of $P^\circ$, with columns scaled by positive weights, which is the identification made on p. 9. Only the first sentence of Theorem 3.3 is stated; the converse is not. The hypothesis $n \ge 1$ excludes a degenerate case in which the printed statement fails: in $\mathbb R^0$ the point $P=\{0\}$ has the proper $\mathbb R^m$-lift $\pi = 0$, $L = \mathbb R^m$, but $(\mathbb R^m)^* = \{0\}$ cannot factor its slack matrix $(1)$.
-- source:
--   Gouveia, Parrilo & Thomas, Lifts of Convex Sets and Cone Factorizations, arXiv:1111.3164v2, p. 9, Theorem 3.3 (first sentence)

import Mathlib
import Definitions.Def_ConeLifts_StableSet_HasConeLift
import Definitions.Def_ConeLifts_Shared_polar
import Definitions.Def_ConeLifts_StableSet_IsSlackMatrix
import Definitions.Def_ConeLifts_StableSet_HasConeFactorization

namespace ConeLifts.StableSet

/-- **Theorem 3.3, first sentence** (Gouveia, Parrilo & Thomas, arXiv:1111.3164v2, p. 9): if a
full-dimensional polytope `P` has a proper `K`-lift then every slack matrix of `P` admits a
`K`-factorization.

`K ⊆ ℝᵐ` is a full-dimensional closed convex cone (Definition 2.1, p. 3). `P ⊆ ℝⁿ` is the convex
hull of a finite set with the origin in its interior (the standing assumption of §3, p. 9, which
also makes `P` full-dimensional), in a space of positive dimension `n ≥ 1`: for `n = 0` the point
`P = {0} = ℝ⁰` has the proper `ℝᵐ`-lift `π = 0`, `L = ℝᵐ`, while `(ℝᵐ)* = {0}` cannot factor its
slack matrix `(1)`. The slack matrices of `P` are encoded by `IsSlackMatrix`: the
canonical slack matrix `(1 - ⟨p, y⟩)` on `ext(P) × ext(P°)` with positively scaled columns. -/
theorem polytope_slackMatrix_coneFactorization {n m : ℕ} (hn : 1 ≤ n)
    (K : Set (EuclideanSpace ℝ (Fin m)))
    (hK_closed : IsClosed K) (hK_convex : Convex ℝ K)
    (hK_cone : ∀ t : ℝ, 0 ≤ t → ∀ x ∈ K, t • x ∈ K)
    (hK_full : (interior K).Nonempty)
    (P : Set (EuclideanSpace ℝ (Fin n)))
    (hP_polytope : ∃ V : Finset (EuclideanSpace ℝ (Fin n)),
      P = convexHull ℝ (V : Set (EuclideanSpace ℝ (Fin n))))
    (hP_origin : (0 : EuclideanSpace ℝ (Fin n)) ∈ interior P)
    (hlift : HasProperConeLift K P)
    (M : Matrix (Set.extremePoints ℝ P) (Set.extremePoints ℝ (ConeLifts.Shared.polar P)) ℝ)
    (hM : IsSlackMatrix P M) :
    HasConeFactorization K M := by sorry

end ConeLifts.StableSet
