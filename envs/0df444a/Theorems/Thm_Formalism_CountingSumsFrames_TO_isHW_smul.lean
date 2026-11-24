-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_TO_isHW_smul
-- name    : Formalism.CountingSumsFrames.TO.isHW_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:39:01.769809+00:00
-- url     : https://prove2.me/theorems/be4d327b-9203-4c59-8dea-82964dcefa40
-- title:
--   TO: is HW smul
-- statement:
--   The TO construction uses the is HW smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L3094-L3097
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L3094-L3097

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
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem Formalism.CountingSumsFrames.TO.isHW_smul (L : Letters N) (j : ℕ) (la : Fin r → ℤ) (c : ℚ_[p]) {x : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (hx : (GA p L j).IsHW la x) : (GA p L j).IsHW la (c • x) := by sorry
