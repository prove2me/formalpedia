-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_ETerm_fact_dvd
-- name    : Formalism.InvariantFactorPaths.G7.ETerm.fact_dvd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:34:08.265047+00:00
-- url     : https://prove2.me/theorems/89ac88e6-b7bf-48da-a000-3aed1c34e5a3
-- title:
--   ETerm: fact dvd
-- statement:
--   The ETerm construction uses the fact dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/NormNatCastLeOfDvd.lean#L286-L314
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/NormNatCastLeOfDvd.lean#L286-L314

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

theorem Formalism.InvariantFactorPaths.G7.ETerm.fact_dvd {Φ κ : Type} [Fintype Φ] [Fintype κ] (k : Φ ⊕ κ ⊕ Fin 2 → ℕ) :
    (∑ x : κ, k (Sum.inr (Sum.inl x))).factorial ∣
      Nat.multinomial univ k * ∏ x : κ, (k (Sum.inr (Sum.inl x))).factorial := by sorry
