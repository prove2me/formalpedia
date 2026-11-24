-- Prove2me | Theorems.Thm_Formalism_REAL_iteratedGrowthBound_holds
-- name    : Formalism.REAL.iteratedGrowthBound_holds
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T10:23:17.917375+00:00
-- url     : https://prove2.me/theorems/6662e04e-69a8-4a46-8e01-22e031a051d9
-- title:
--   REAL: iterated Growth Bound holds
-- statement:
--   The REAL construction uses the iterated Growth Bound holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/QuadraticInequalityBoundHolds.lean#L9-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/QuadraticInequalityBoundHolds.lean#L9-L31

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementA
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuadraticInequalityBoundHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.REAL

theorem Formalism.REAL.iteratedGrowthBound_holds : GrowthIter := by sorry
