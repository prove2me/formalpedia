-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLawNegation_integral_X
-- name    : Formalism.InvariantFactorPaths.G7.FormalGroupLawNegation.integral_X
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:00:47.815047+00:00
-- url     : https://prove2.me/theorems/87491ea1-0299-4d3d-b744-0a9c43bc8142
-- title:
--   Formal Group Law Negation: integral X
-- statement:
--   The Formal Group Law Negation construction uses the integral X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/KOneConsequenceOf.lean#L18-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/KOneConsequenceOf.lean#L18-L23

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_CoeffSubstLgFOfDegreeOne
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_KOneConsequenceOf
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
open Formalism.InvariantFactorPaths.G7.FormalGroupLawNegation
open FormalGroupLaws

theorem Formalism.InvariantFactorPaths.G7.FormalGroupLawNegation.integral_X {K ι : Type} [NormedField K] (x : ι) :
    Integral (MvPowerSeries.X x : MvPowerSeries ι K) := by sorry
