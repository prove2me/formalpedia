-- Prove2me | Theorems.Thm_Formalism_RankGapBounds_ChebyshevFactorialBounds_chebyshevThetaLe_holds
-- name    : Formalism.RankGapBounds.ChebyshevFactorialBounds.chebyshevThetaLe_holds
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:25:21.035223+00:00
-- url     : https://prove2.me/theorems/b00df9a8-dcd4-458d-bd7f-2381e44c2213
-- title:
--   Chebyshev Factorial Bounds: chebyshev Theta Le holds
-- statement:
--   The Chebyshev Factorial Bounds construction uses the chebyshev Theta Le holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RankGapBounds/RankGapProofs/CardLargePrimeFactorsLeOneHolds.lean#L7-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RankGapBounds/RankGapProofs/CardLargePrimeFactorsLeOneHolds.lean#L7-L11

import Definitions.Def_Formalism_RankGapBounds_LargePrimeFactor
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_CardLargePrimeFactorsLeOneHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Real Finset
open Formalism Formalism.RankGapBounds Formalism.RankGapBounds.ChebyshevFactorialBounds

theorem Formalism.RankGapBounds.ChebyshevFactorialBounds.chebyshevThetaLe_holds : ChebyshevTheta := by sorry
