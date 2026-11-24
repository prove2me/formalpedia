-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_TO_glAct_isF
-- name    : Formalism.CountingSumsFrames.TO.glAct_isF
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:35:48.254831+00:00
-- url     : https://prove2.me/theorems/3f7e186d-e265-45c1-b310-a6327876298f
-- title:
--   TO: gl Act is F
-- statement:
--   The TO construction uses the gl Act is F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L722-L725
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L722-L725

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
open MvPolynomial Finset Formalism.GM.DimensionMonotonicity Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem Formalism.CountingSumsFrames.TO.glAct_isF (L : Letters N) (j0 J : ℕ) (c d : Fin r) {g : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (hg : IsF (fsj N r j0) g) : IsF (fsj N r j0) (glAct p L J c d g) := by sorry
