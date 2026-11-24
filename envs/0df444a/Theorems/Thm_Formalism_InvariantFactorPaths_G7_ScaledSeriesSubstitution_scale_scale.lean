-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_ScaledSeriesSubstitution_scale_scale
-- name    : Formalism.InvariantFactorPaths.G7.ScaledSeriesSubstitution.scale_scale
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:41:24.463496+00:00
-- url     : https://prove2.me/theorems/b801db67-fad5-4a85-ae2b-92b077da318b
-- title:
--   Scaled Series Substitution: scale scale
-- statement:
--   The Scaled Series Substitution construction uses the scale scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/EChain.lean#L19-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/EChain.lean#L19-L25

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementJ
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EJoint
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_NormLiftLeOne
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_OmegaOfTraceDuality
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EChain
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
open Formalism.DworkPowerSeriesWeights (Integral mvExp frameJet)
open Formalism.GrowthSums (gamP rhoP gainG excessGain)
open Formalism.InvariantFactorPaths.G7.ScaledSeriesSubstitution

theorem Formalism.InvariantFactorPaths.G7.ScaledSeriesSubstitution.scale_scale {K ι : Type} [Field K] {ϖ : K} (hϖ : ϖ ≠ 0) (f : MvPowerSeries ι K) :
    MvPowerSeries.subst (fun i => MvPowerSeries.C ϖ * (MvPowerSeries.X i : MvPowerSeries ι K))
      (MvPowerSeries.subst
        (fun i => MvPowerSeries.C ϖ⁻¹ * (MvPowerSeries.X i : MvPowerSeries ι K)) f) = f := by sorry
