-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_shiftLastLetterThresholds_add
-- name    : Formalism.InvariantFactorPaths.L4.shiftLastLetterThresholds_add
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T02:40:11.643979+00:00
-- url     : https://prove2.me/theorems/80120641-b191-40eb-bb9b-6d706ce70520
-- title:
--   L4: shift Last Letter Thresholds add
-- statement:
--   The L4 construction uses the shift Last Letter Thresholds add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/GramBoundUnconditionalOfSat.lean#L122-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/GramBoundUnconditionalOfSat.lean#L122-L131

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementG
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementF
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_MulEarlyModP
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_DischargeHeightBound
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_FinalM
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_GramBoundUnconditionalOfSat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames Formalism.InvariantFactorPaths.PW MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {K r : ℕ} [NeZero r]

theorem Formalism.InvariantFactorPaths.L4.shiftLastLetterThresholds_add {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (a b : ℕ) :
    shiftLastLetterThresholds K J (shiftLastLetterThresholds K J M a) b = shiftLastLetterThresholds K J M (a + b) := by sorry
