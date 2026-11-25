-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_takeD_vec_last
-- name    : Formalism.InvariantFactorPaths.L4.takeD_vec_last
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:10:09.256095+00:00
-- url     : https://prove2.me/theorems/b5c9a65c-6dc6-4614-a9c6-46738d077e81
-- title:
--   L4: take D vec last
-- statement:
--   The L4 construction uses the take D vec last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/GramBoundUnconditionalOfSat.lean#L258-L261
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/GramBoundUnconditionalOfSat.lean#L258-L261

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

theorem Formalism.InvariantFactorPaths.L4.takeD_vec_last (LL : Letters N) (T : TieData) (hadm : T.Admissible LL) (n : Fin T.t → ℕ) (i : Fin T.t) :
    ((LL.setTies T n).takeD (T.pos i + 1)).vec (Fin.last (T.pos i)) = true := by sorry
