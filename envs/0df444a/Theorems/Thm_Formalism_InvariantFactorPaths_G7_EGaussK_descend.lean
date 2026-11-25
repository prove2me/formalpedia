-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_EGaussK_descend
-- name    : Formalism.InvariantFactorPaths.G7.EGaussK.descend
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T02:04:31.774649+00:00
-- url     : https://prove2.me/theorems/21e28db3-a0e5-5fb7-80f7-11a473d80148
-- title:
--   EGauss K: descend
-- statement:
--   The EGauss K construction uses the descend property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/EGaussK.lean#L132-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/EGaussK.lean#L132-L144

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementGK
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_KernelFromKOne
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EGaussK
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DeterminantJetScaling_descend

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
open Formalism.DworkPowerSeriesWeights (Integral mvExp frameJet jetPair minorProd)
open Formalism.GrowthSums (gamP rhoP gainG excessGain)
open Formalism.InvariantFactorPaths.G7.EGaussK
open EGauss

theorem Formalism.InvariantFactorPaths.G7.EGaussK.descend {K : Type} [NormedField K] {p : ℕ} [hp : Fact p.Prime]
    (hn : ‖(p : K)‖ = (p : ℝ)⁻¹) {ϖ : K} (hϖ : ϖ ^ (p ^ 2 - 1) = (p : K))
    (d : ℕ) (g : ℝ) (x y : K) (hxy : x = ϖ ^ d * y)
    (hx : ‖x‖ ≤ (p : ℝ) ^ (-(g + rhoP p * d))) : ‖y‖ ≤ (p : ℝ) ^ (-g) := by sorry
