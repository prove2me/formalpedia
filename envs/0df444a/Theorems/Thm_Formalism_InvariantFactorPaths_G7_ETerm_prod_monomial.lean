-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_ETerm_prod_monomial
-- name    : Formalism.InvariantFactorPaths.G7.ETerm.prod_monomial
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:27:27.298512+00:00
-- url     : https://prove2.me/theorems/fe910a87-62d1-4e0d-a5af-375c47e15c8a
-- title:
--   ETerm: prod monomial
-- statement:
--   The ETerm construction uses the prod monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/NormNatCastLeOfDvd.lean#L189-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/NormNatCastLeOfDvd.lean#L189-L197

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

theorem Formalism.InvariantFactorPaths.G7.ETerm.prod_monomial {α : Type} (s : Finset α) (d : α → σ →₀ ℕ) (a : α → K) :
    ∏ i ∈ s, MvPowerSeries.monomial (d i) (a i) =
      MvPowerSeries.monomial (∑ i ∈ s, d i) (∏ i ∈ s, a i) := by sorry
