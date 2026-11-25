-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_pos_num
-- name    : Formalism.InvariantFactorPaths.L4.pos_num
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T02:22:04.755036+00:00
-- url     : https://prove2.me/theorems/dcba234a-205a-52ae-9e1d-858b88e74176
-- title:
--   L4: pos num
-- statement:
--   The L4 construction uses the pos num property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/GramBoundUnconditionalOfSat.lean#L297-L307
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/GramBoundUnconditionalOfSat.lean#L297-L307

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
variable {N : ℕ}

theorem Formalism.InvariantFactorPaths.L4.pos_num (LL : Letters N) (T : TieData) (hadm : T.Admissible LL) (p a r : ℕ) (i : Fin T.t) :
    (((T.pos i : ℕ) + 3) * r ^ 2 : ℝ) * lgV2 p a r ≤ ((N + 2) * r ^ 2 : ℝ) * lgV2 p a r := by sorry
