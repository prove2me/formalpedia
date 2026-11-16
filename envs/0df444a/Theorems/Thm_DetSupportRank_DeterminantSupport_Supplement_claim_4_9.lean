-- Prove2me | Theorems.Thm_DetSupportRank_DeterminantSupport_Supplement_claim_4_9
-- name    : DetSupportRank.DeterminantSupport.Supplement.claim_4_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:10:47.522722+00:00
-- url     : https://prove2.me/theorems/bb33809f-7a29-45f5-9055-693e3d9300ec
-- title:
--   Claim 4.9 — Dense alternating matrix has Pfaffian one
-- statement:
--   Let $F$ be any field and $n\ge0$ even. For the dense alternating matrix with zero diagonal, ones above the diagonal and minus ones below,
--   $$\operatorname{pf}(K_n)=1.$$
--   The empty matrix is included. This value supplies the dense-matrix specialization used in formula (4) of Theorem 4.3.
--
--   Differences from the source:
--   - encoding: one-based indices in [n] → zero-based indices Fin n; reason: the increasing bijection preserves rows, columns and complements; paper i becomes r.val+1, also in signs
--   - encoding: signed sum over ordered pair partitions → signed sum over their unique canonical permutations; reason: pairs occupy even-odd consecutive positions, are oriented increasingly and are ordered by first endpoint, exactly as equation (3); no multiplicity or division
-- source:
--   Neil Krishnan, Guy Moshkovitz, Optimal partition rank bounds for the determinant and other multilinear polynomials, STOC 2027 submission #631 (October 2026), Claim 4.9, p. 11 (PDF p. 11); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/631.pdf

import Definitions.Def_DetSupportRank_DeterminantSupport_Supplement_Pfaffian
import Definitions.Def_DetSupportRank_DeterminantSupport_Supplement_SpecialMatrices

noncomputable section
open scoped BigOperators

namespace DetSupportRank.DeterminantSupport.Supplement

/-- Claim 4.9, p.11; the proof p.12 includes the empty matrix. -/
theorem claim_4_9 {F : Type*} [Field F] (n : ℕ) (he : Even n) :
    pfaffian (denseK F n) = 1 := by sorry

end DetSupportRank.DeterminantSupport.Supplement
