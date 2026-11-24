-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_TO_isHW_iff
-- name    : Formalism.CountingSumsFrames.TO.isHW_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:33:54.562892+00:00
-- url     : https://prove2.me/theorems/1558e99a-5e28-4940-82ab-9dc52e85bee8
-- title:
--   TO: is HW iff
-- statement:
--   The TO construction uses the is HW iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L1226-L1235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L1226-L1235

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

theorem Formalism.CountingSumsFrames.TO.isHW_iff (L : Letters N) (j : ℕ) (la : Fin r → ℤ) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    (GA p L j).IsHW la x ↔ x ∈ HWC p L j univ la := by sorry
