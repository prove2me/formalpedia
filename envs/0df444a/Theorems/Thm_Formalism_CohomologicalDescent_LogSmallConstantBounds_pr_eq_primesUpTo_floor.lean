-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_pr_eq_primesUpTo_floor
-- name    : Formalism.CohomologicalDescent.LogSmallConstantBounds.pr_eq_primesUpTo_floor
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T22:44:21.367035+00:00
-- url     : https://prove2.me/theorems/bcabf646-5954-41f9-95ac-4c0b4420d125
-- title:
--   Log Small Constant Bounds: pr eq primes Up To floor
-- statement:
--   The Log Small Constant Bounds construction uses the pr eq primes Up To floor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ParameterBounds.lean#L1111-L1111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ParameterBounds.lean#L1111-L1111

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

theorem Formalism.CohomologicalDescent.LogSmallConstantBounds.pr_eq_primesUpTo_floor (y : ℝ) : pr y = Formalism.RankGapBounds.ChebyshevFactorialBounds.primesUpTo ⌊y⌋₊ := by sorry
