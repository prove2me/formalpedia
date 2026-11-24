-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_ScaledSeriesSubstitution_constantCoeff_zLin
-- name    : Formalism.InvariantFactorPaths.G7.ScaledSeriesSubstitution.constantCoeff_zLin
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T10:56:48.031922+00:00
-- url     : https://prove2.me/theorems/373814dd-2d25-4bbd-a4b6-87a4ca49b380
-- title:
--   Scaled Series Substitution: constant Coeff z Lin
-- statement:
--   The Scaled Series Substitution construction uses the constant Coeff z Lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/EChain.lean#L37-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/EChain.lean#L37-L43

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementJ
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EJoint
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_NormLiftLeOne
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_OmegaOfTraceDuality
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EChain
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_constantCoeff_zLin

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

theorem Formalism.InvariantFactorPaths.G7.ScaledSeriesSubstitution.constantCoeff_zLin {K : Type} [Field K] {ν r0 r1 : ℕ} [NeZero ν]
    (om oms : Fin ν → ZMod (2 * ν) → K) (x : Bool × EV ν r0 r1) :
    MvPowerSeries.constantCoeff (zLin om oms x) = 0 := by sorry
