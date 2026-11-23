-- Prove2me | Theorems.Thm_ConeLifts_Factorization_Supplement_polytope_factorization_theorem
-- name    : ConeLifts.Factorization.Supplement.polytope_factorization_theorem
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T10:49:04.904378+00:00
-- url     : https://prove2.me/theorems/c70cdce5-6c0f-408a-8283-c1462f883c91
-- title:
--   Theorem 3.3 (corrected: n ≥ 1 in the forward half) — cone lifts of polytopes and cone factorizations of slack matrices
-- statement:
--   Let $K \subseteq \mathbb R^m$ be a full-dimensional closed convex cone and $P \subseteq \mathbb R^n$ a polytope (the convex hull of finitely many points) with the origin in its interior. A **slack matrix** of $P$ is the matrix $(h_j(p_i))$ of a facet inequality representation $P = \{x : h_1(x) \ge 0, \dots, h_f(x) \ge 0\}$, rows indexed by the vertices $p_i$; a **$K$-factorization** of a matrix $M$ consists of $a^i \in K$ and $b^j \in K^*$ with $\langle a^i, b^j\rangle = M_{ij}$. Then:
--
--   1. if $n \ge 1$ and $P$ has a proper $K$-lift, every slack matrix of $P$ admits a $K$-factorization;
--   2. if some slack matrix of $P$ has a $K$-factorization, then $P$ has a $K$-lift.
--
--   $$
--   P = \pi(K \cap L),\ L \cap \operatorname{int} K \neq \emptyset \;\Longrightarrow\; S_P = (\langle a^i, b^j\rangle) \;\Longrightarrow\; P = \pi'(K \cap L').
--   $$
--
--   This is the polytope form of Theorem 2.4 and generalizes Yannakakis's theorem from nonnegative orthants to arbitrary closed convex cones.
--
--   **Formalization Note** The vocabulary is that of the published mission on stable set polytopes: slack matrices are the canonical slack matrix $(1 - \langle p, y\rangle)$ on $\operatorname{ext}(P) \times \operatorname{ext}(P^\circ)$ with positively scaled columns.
--
--   Differences from the source:
--   - correction: no dimension condition → the first part assumes $n \ge 1$; reason: for $n = 0$, $P = \{0\} = \mathbb R^0$ has a proper $\mathbb R^m$-lift but $(\mathbb R^m)^* = \{0\}$ cannot factor its slack matrix $(1)$; the converse keeps $n = 0$
-- source:
--   Gouveia, Parrilo & Thomas, Lifts of Convex Sets and Cone Factorizations, arXiv:1111.3164v2, p. 9, Theorem 3.3

import Mathlib
import Definitions.Def_ConeLifts_StableSet_HasConeLift
import Definitions.Def_ConeLifts_Shared_polar
import Definitions.Def_ConeLifts_StableSet_IsSlackMatrix
import Definitions.Def_ConeLifts_StableSet_HasConeFactorization

namespace ConeLifts.Factorization.Supplement

open ConeLifts.StableSet

/-- **Theorem 3.3** of Gouveia, Parrilo & Thomas, arXiv:1111.3164v2, p. 9: "If a full-dimensional
polytope P has a proper K-lift then every slack matrix of P admits a K-factorization. Conversely,
if some slack matrix of P has a K-factorization then P has a K-lift."

`K ⊆ ℝᵐ` is a full-dimensional closed convex cone (Definition 2.1, p. 3). `P ⊆ ℝⁿ` is the convex
hull of a finite set with the origin in its interior (§3, p. 9). The slack matrices of `P` are the
canonical slack matrix `(1 − ⟨p, y⟩)` on `ext(P) × ext(P°)` with positively scaled columns
(`IsSlackMatrix`, Definition 3.1). Recorded repair, first sentence only: `1 ≤ n` (for `n = 0`,
`P = {0}` has a proper `ℝᵐ`-lift while `(ℝᵐ)* = {0}` cannot factor its slack matrix `(1)`). -/
theorem polytope_factorization_theorem {n m : ℕ}
    (K : Set (EuclideanSpace ℝ (Fin m)))
    (hK_closed : IsClosed K) (hK_convex : Convex ℝ K)
    (hK_cone : ∀ t : ℝ, 0 ≤ t → ∀ x ∈ K, t • x ∈ K)
    (hK_full : (interior K).Nonempty)
    (P : Set (EuclideanSpace ℝ (Fin n)))
    (hP_polytope : ∃ V : Finset (EuclideanSpace ℝ (Fin n)),
      P = convexHull ℝ (V : Set (EuclideanSpace ℝ (Fin n))))
    (hP_origin : (0 : EuclideanSpace ℝ (Fin n)) ∈ interior P) :
    (1 ≤ n → HasProperConeLift K P →
      ∀ M : Matrix (Set.extremePoints ℝ P) (Set.extremePoints ℝ (ConeLifts.Shared.polar P)) ℝ,
        IsSlackMatrix P M → HasConeFactorization K M) ∧
    ((∃ M : Matrix (Set.extremePoints ℝ P) (Set.extremePoints ℝ (ConeLifts.Shared.polar P)) ℝ,
        IsSlackMatrix P M ∧ HasConeFactorization K M) → HasConeLift K P) := by sorry

end ConeLifts.Factorization.Supplement
