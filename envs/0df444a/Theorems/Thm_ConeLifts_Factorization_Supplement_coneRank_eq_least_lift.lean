-- Prove2me | Theorems.Thm_ConeLifts_Factorization_Supplement_coneRank_eq_least_lift
-- name    : ConeLifts.Factorization.Supplement.coneRank_eq_least_lift
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T10:50:05.012585+00:00
-- url     : https://prove2.me/theorems/2d152b38-7fdb-4d9b-b6bb-4994093f271e
-- title:
--   Theorem 4.4 (corrected: n ≥ 1) — the cone rank of a convex body is the smallest index of a lift
-- statement:
--   Let $\mathcal K = (K_i)_{i \ge 0}$ be a closed cone family and $C \subseteq \mathbb R^n$, $n \ge 1$, a convex body. Then the $\mathcal K$-rank of $C$ (the smallest $i$ such that the slack operator $S_C$ has a $K_i$-factorization) equals the smallest $i$ such that $C$ has a $K_i$-lift:
--
--   $$
--   \operatorname{rank}_{\mathcal K}(C) = \min\{\, i \in \mathbb N : C = \pi(K_i \cap L) \text{ for some affine } L \text{ and linear } \pi \,\},
--   $$
--
--   where both sides are $+\infty$ when no index works.
--
--   The theorem turns the cone rank, defined algebraically through factorizations, into the geometric size of the smallest lift within the family; for orthants and psd cones it identifies the nonnegative and psd ranks with the smallest polyhedral and spectrahedral lifts.
--
--   **Formalization Note** Both minima are infima in `ℕ∞` over the indices with the property, `⊤` when there is none.
--
--   Differences from the source:
--   - correction: no dimension condition → $n \ge 1$; reason: for $n = 0$ and $K_0 = \mathbb R^0_+ = \{0\}$ the body $C = \{0\} = \mathbb R^0$ has a $K_0$-lift but rank at least $1$, the exception of the published Theorem 2.4
-- source:
--   Gouveia, Parrilo & Thomas, Lifts of Convex Sets and Cone Factorizations, arXiv:1111.3164v2, p. 13, Theorem 4.4

import Mathlib
import Definitions.Def_ConeLifts_Factorization_IsConvexBody
import Definitions.Def_ConeLifts_Factorization_HasLift
import Definitions.Def_ConeLifts_Factorization_Supplement_ConeFamily
import Definitions.Def_ConeLifts_Factorization_Supplement_coneRank

namespace ConeLifts.Factorization.Supplement

/-- **Theorem 4.4** of Gouveia, Parrilo & Thomas, arXiv:1111.3164v2, p. 13: "Let 𝒦 = (K_i)_{i≥0}
be a closed cone family and C ⊂ ℝⁿ a convex body. Then rank_𝒦(C) is the smallest i such that C
has a K_i-lift."

The smallest index is taken in `ℕ∞`, `⊤` when no `Kᵢ`-lift exists, so the two infinite cases
coincide as well. Recorded repair: `1 ≤ n`, as in Theorem 2.4 (for `n = 0` and `K₀ = ℝ⁰₊ = {0}`,
`C = {0} = ℝ⁰` has a `K₀`-lift but `𝒦`-rank at least `1`). -/
theorem coneRank_eq_least_lift {n : ℕ} (hn : 1 ≤ n) (𝒦 : ConeFamily) (h𝒦 : 𝒦.IsClosed)
    (C : Set (EuclideanSpace ℝ (Fin n))) (hC : ConeLifts.Factorization.IsConvexBody C) :
    coneRank 𝒦 C =
      ⨅ (i : ℕ) (_ : ConeLifts.Factorization.HasLift (𝒦.cone i) C), (i : ℕ∞) := by sorry

end ConeLifts.Factorization.Supplement
