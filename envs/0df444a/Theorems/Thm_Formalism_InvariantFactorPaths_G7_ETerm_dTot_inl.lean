-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_ETerm_dTot_inl
-- name    : Formalism.InvariantFactorPaths.G7.ETerm.dTot_inl
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:27:32.89591+00:00
-- url     : https://prove2.me/theorems/d6398820-7b88-432f-b3ce-d26e6d21520c
-- title:
--   ETerm: d Tot inl
-- statement:
--   The ETerm construction uses the d Tot inl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/NormNatCastLeOfDvd.lean#L345-L348
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/NormNatCastLeOfDvd.lean#L345-L348

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
variable {K Tp Lw Φ κ : Type} [NormedField K] [IsUltrametricDist K] [Fintype Tp] [Fintype Lw]
  [Fintype Φ] [Fintype κ]

theorem Formalism.InvariantFactorPaths.G7.ETerm.dTot_inl (dA : Φ → Tp →₀ ℕ) (dB : κ → Tp →₀ ℕ) (k : Φ ⊕ κ ⊕ Fin 2 → ℕ) (τ : Tp) :
    dTot (Lw := Lw) dA dB k (Sum.inl τ) =
      ∑ φ, k (Sum.inl φ) * dA φ τ + ∑ x, k (Sum.inr (Sum.inl x)) * dB x τ := by sorry
