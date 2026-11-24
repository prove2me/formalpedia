-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_BetaIsG_of
-- name    : Formalism.InvariantFactorPaths.G7.BetaIsG_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:25:59.722504+00:00
-- url     : https://prove2.me/theorems/7a96a07b-22e6-4286-8f9a-c14f55c2edc6
-- title:
--   G7: Beta Is G of
-- statement:
--   The G7 construction uses the Beta Is G of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/NormLiftLeOne.lean#L32-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/NormLiftLeOne.lean#L32-L56

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_NormLiftLeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral mvExp)

theorem Formalism.InvariantFactorPaths.G7.BetaIsG_of (h0 : StepZero) (h1 : StepI) (h2 : StepII) (hH : StepH) (h3 : StepIII)
    (h4 : StepIV) (hSw : SwapRules) (hS : SimeqRules) : BetaIsG := by sorry
