-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_ETerm_closure_sum
-- name    : Formalism.InvariantFactorPaths.G7.ETerm.closure_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:54:15.981824+00:00
-- url     : https://prove2.me/theorems/6a85cd30-8c9c-43a9-82be-81c0d0970f62
-- title:
--   ETerm: closure sum
-- statement:
--   The ETerm construction uses the closure sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/NormNatCastLeOfDvd.lean#L267-L277
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/NormNatCastLeOfDvd.lean#L267-L277

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_NormNatCastLeOfDvd
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_C_mul_right
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_eq_sum
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_sum_right

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
open Formalism.InvariantFactorPaths.G7.ETerm
open Formalism.DworkPowerSeriesWeights (Integral jetPair mfact jetPair_eq_sum jetPair_C_mul_right jetPair_sum_right)
variable {K : Type} [NormedField K] [IsUltrametricDist K]

theorem Formalism.InvariantFactorPaths.G7.ETerm.closure_sum {Wt J : Type} (valid : Wt → Prop) (B : Wt → ℝ) (s : Finset J) (f : J → K)
    (h : ∀ j ∈ s, f j = 0 ∨ ∃ w, valid w ∧ ‖f j‖ ≤ B w) :
    ∑ j ∈ s, f j = 0 ∨ ∃ w, valid w ∧ ‖∑ j ∈ s, f j‖ ≤ B w := by sorry
