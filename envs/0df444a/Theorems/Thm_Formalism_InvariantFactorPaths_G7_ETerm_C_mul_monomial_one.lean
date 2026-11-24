-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_ETerm_C_mul_monomial_one
-- name    : Formalism.InvariantFactorPaths.G7.ETerm.C_mul_monomial_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:27:39.197927+00:00
-- url     : https://prove2.me/theorems/af66d0e8-35cf-4d8b-8912-d5ecdc2808ec
-- title:
--   ETerm: C mul monomial one
-- statement:
--   The ETerm construction uses the C mul monomial one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/NormNatCastLeOfDvd.lean#L199-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/NormNatCastLeOfDvd.lean#L199-L202

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
variable {K σ : Type} [Field K]

theorem Formalism.InvariantFactorPaths.G7.ETerm.C_mul_monomial_one (a : K) (d : σ →₀ ℕ) :
    MvPowerSeries.C a * MvPowerSeries.monomial d (1 : K) = MvPowerSeries.monomial d a := by sorry
