-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_sum_log_div_le_log_add_log_four
-- name    : Formalism.CohomologicalDescent.LogSmallConstantBounds.sum_log_div_le_log_add_log_four
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:44:56.312429+00:00
-- url     : https://prove2.me/theorems/771a26f1-df04-4583-91d0-7e72896ec6ce
-- title:
--   Log Small Constant Bounds: sum log div le log add log four
-- statement:
--   The Log Small Constant Bounds construction uses the sum log div le log add log four property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ParameterBounds.lean#L1160-L1193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ParameterBounds.lean#L1160-L1193

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

theorem Formalism.CohomologicalDescent.LogSmallConstantBounds.sum_log_div_le_log_add_log_four (n : ℕ) (hn : 1 ≤ n) :
    ∑ p ∈ Formalism.RankGapBounds.ChebyshevFactorialBounds.primesUpTo n, Real.log (p : ℝ) / (p : ℝ) ≤
      Real.log (n : ℝ) + Real.log 4 := by sorry
