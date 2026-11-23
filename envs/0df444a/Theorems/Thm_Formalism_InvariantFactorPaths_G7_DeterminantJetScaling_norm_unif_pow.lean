-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_DeterminantJetScaling_norm_unif_pow
-- name    : Formalism.InvariantFactorPaths.G7.DeterminantJetScaling.norm_unif_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:25:03.661926+00:00
-- url     : https://prove2.me/theorems/e4de543a-0b46-4e7e-a218-0169fea397f5
-- title:
--   Determinant Jet Scaling: norm unif pow
-- statement:
--   The Determinant Jet Scaling construction uses the norm unif pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/EKernel.lean#L86-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/EKernel.lean#L86-L98

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementH
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EJoint
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartB
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EKernel
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
open Formalism.DworkPowerSeriesWeights (Integral frameJet jetPairPoly minorProd mfact)
open Formalism.GrowthSums (gamP rhoP gainG excessGain)
open Formalism.InvariantFactorPaths.G7.DeterminantJetScaling

theorem Formalism.InvariantFactorPaths.G7.DeterminantJetScaling.norm_unif_pow {p : ℕ} [hp : Fact p.Prime] {ϖ : ℂ_[p]} (hϖ : ϖ ^ (p ^ 2 - 1) = (p : ℂ_[p]))
    (d : ℕ) : ‖ϖ ^ d‖ = (p : ℝ) ^ (-(rhoP p * d)) := by sorry
