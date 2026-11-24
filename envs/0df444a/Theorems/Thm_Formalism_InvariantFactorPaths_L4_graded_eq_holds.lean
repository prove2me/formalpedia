-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_graded_eq_holds
-- name    : Formalism.InvariantFactorPaths.L4.graded_eq_holds
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:43:34.601642+00:00
-- url     : https://prove2.me/theorems/2549d164-dbfd-4c83-932c-70581fcd8636
-- title:
--   L4: graded eq holds
-- statement:
--   The L4 construction uses the graded eq holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/FiltrationBotHolds.lean#L306-L328
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/FiltrationBotHolds.lean#L306-L328

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementB
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_MulEarlyLettersHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_InitPartZeroXMul
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FiltrationBotHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset

theorem Formalism.InvariantFactorPaths.L4.graded_eq_holds : GrEq := by sorry
