-- Prove2me | Theorems.Thm_Formalism_DimensionVariation_stepDiProd6
-- name    : Formalism.DimensionVariation.stepDiProd6
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:24:34.776017+00:00
-- url     : https://prove2.me/theorems/c88ffc07-f326-5916-8d1f-471266abb300
-- title:
--   Dimension Variation: step Di Prod6
-- statement:
--   The Dimension Variation construction uses the step Di Prod6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaSupremumBounds/DivIneqRecordTwoConst6.lean#L20-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaSupremumBounds/DivIneqRecordTwoConst6.lean#L20-L20

import Definitions.Def_Formalism_ThetaSupremumBounds_LiftOperatorBoundOfFockJet
import Definitions.Def_Formalism_ThetaSupremumBounds_FinalJ
import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_GlobalBoundRefinements
import Definitions.Def_Formalism_ThetaSupremumBounds_DivIneqRecordTwoConst6
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped Real
open Formalism Formalism.DimensionVariation
open Formalism.LatticeIndexTer (ph)

theorem Formalism.DimensionVariation.stepDiProd6 : StepDiProd6 := by sorry
