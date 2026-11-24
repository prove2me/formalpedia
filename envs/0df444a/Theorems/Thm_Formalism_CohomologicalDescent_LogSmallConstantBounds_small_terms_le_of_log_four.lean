-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_small_terms_le_of_log_four
-- name    : Formalism.CohomologicalDescent.LogSmallConstantBounds.small_terms_le_of_log_four
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T22:44:47.308375+00:00
-- url     : https://prove2.me/theorems/233f1657-54d7-47fb-9289-77cff3564cd7
-- title:
--   Log Small Constant Bounds: small terms le of log four
-- statement:
--   The Log Small Constant Bounds construction uses the small terms le of log four property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ParameterBounds.lean#L1251-L1264
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ParameterBounds.lean#L1251-L1264

import Definitions.Def_Formalism_PieriBlockIdeals_MertensReciprocalElementary
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SharperSizeNeedsMleKFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LocalComponentGL
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LogarithmEquivalence
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_CardLargePrimeFactorsLeOneHolds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LogSmallConstantBounds
open Classical

theorem Formalism.CohomologicalDescent.LogSmallConstantBounds.small_terms_le_of_log_four {P : Par} (H : P.Hyp) (G : P.Large) (s3 s4 : ℝ)
    (h3 : s3 ≤ Real.log (P.h + (P.Nr : ℝ)) + Real.log 4) (h4 : s4 ≤ (P.S + 1) * Real.log P.h) :
    (P.k : ℝ) * P.S * s3 + (P.k : ℝ) * s4 ≤ 2 * (P.k : ℝ) * (P.S + 1) * (P.L + 2) := by sorry
