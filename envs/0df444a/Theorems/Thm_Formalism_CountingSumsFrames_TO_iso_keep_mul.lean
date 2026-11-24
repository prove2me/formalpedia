-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_TO_iso_keep_mul
-- name    : Formalism.CountingSumsFrames.TO.iso_keep_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:39:06.195954+00:00
-- url     : https://prove2.me/theorems/b8112e70-a5fd-49b7-813f-e36945a67dc6
-- title:
--   TO: iso keep mul
-- statement:
--   The TO construction uses the iso keep mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L1827-L1832
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L1827-L1832

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames Formalism.CountingSumsFrames.TO
open Formalism.GM Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem Formalism.CountingSumsFrames.TO.iso_keep_mul (L : Letters N) {j j0 : ℕ} (hj : j ≤ j0) {q : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (hq : IsL (fsj N r j0) q) (la : Fin r → ℤ) :
    ∀ x ∈ IsoC p L j univ la, LinearMap.mulRight ℚ_[p] q x ∈ IsoC p L j univ la := by sorry
