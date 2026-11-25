-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_setLast_deg_last
-- name    : Formalism.InvariantFactorPaths.L4.setLast_deg_last
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T02:08:15.52232+00:00
-- url     : https://prove2.me/theorems/f8e891ac-8999-5f2e-94c0-c5ddf6d22ac0
-- title:
--   L4: set Last deg last
-- statement:
--   The L4 construction uses the set Last deg last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/GramBoundUnconditionalOfSat.lean#L106-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/GramBoundUnconditionalOfSat.lean#L106-L107

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

theorem Formalism.InvariantFactorPaths.L4.setLast_deg_last (LL : Letters (K + 1)) (o : ℕ) : (setLast LL o).deg (Fin.last K) = o := by sorry
