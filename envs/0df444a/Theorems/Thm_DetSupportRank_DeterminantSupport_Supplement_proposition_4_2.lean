-- Prove2me | Theorems.Thm_DetSupportRank_DeterminantSupport_Supplement_proposition_4_2
-- name    : DetSupportRank.DeterminantSupport.Supplement.proposition_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:08:28.810517+00:00
-- url     : https://prove2.me/theorems/964cd7f2-6eba-4444-8727-b2efd567c9d9
-- title:
--   Proposition 4.2 — Even determinant partition-rank upper bound
-- statement:
--   Let $F$ be any field and $n\ge3$ even. For the formal determinant in its $n$ row parts,
--   $$\operatorname{PR}(\det_n)\le n-1.$$
--   This supplies the even-order upper bound in the determinant equality of Theorem 1.2.
--
--   Differences from the source:
--   - encoding: one-based indices in [n] → zero-based indices Fin n; reason: the increasing bijection preserves rows, columns and complements; paper i becomes r.val+1, also in signs
--   - encoding: integer minimum partition-decomposition length → the published partitionRank valued in ℕ∞; reason: it is the infimum of actual decomposition lengths and is finite and attained on the source domain; there is no changed rank notion
-- source:
--   Neil Krishnan, Guy Moshkovitz, Optimal partition rank bounds for the determinant and other multilinear polynomials, STOC 2027 submission #631 (October 2026), Proposition 4.2, p. 10 (PDF p. 10); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/631.pdf

import Definitions.Def_DetSupportRank_DeterminantSupport_PartitionRank
import Definitions.Def_DetSupportRank_DeterminantSupport_Supplement_PolynomialMatrices

noncomputable section
open scoped BigOperators

namespace DetSupportRank.DeterminantSupport.Supplement

/-- Proposition 4.2, p.10: the even-order upper bound, over every field. -/
theorem proposition_4_2 {F : Type*} [Field F] (n : ℕ) (hn : 3 ≤ n) (he : Even n) :
    partitionRank (determinantPolynomial F n) ≤ ((n - 1 : ℕ) : ℕ∞) := by sorry

end DetSupportRank.DeterminantSupport.Supplement
