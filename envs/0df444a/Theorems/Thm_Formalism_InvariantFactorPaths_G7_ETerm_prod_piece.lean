-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_ETerm_prod_piece
-- name    : Formalism.InvariantFactorPaths.G7.ETerm.prod_piece
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:29:17.393348+00:00
-- url     : https://prove2.me/theorems/3a0b34d4-5db0-4f2b-97fe-988de0bc6999
-- title:
--   ETerm: prod piece
-- statement:
--   The ETerm construction uses the prod piece property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/NormNatCastLeOfDvd.lean#L350-L384
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/NormNatCastLeOfDvd.lean#L350-L384

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

theorem Formalism.InvariantFactorPaths.G7.ETerm.prod_piece (p : ℕ) (Z Y : MvPowerSeries (Tp ⊕ Lw) K) (aA : Φ → K) (dA : Φ → Tp →₀ ℕ)
    (aB : κ → K) (dB : κ → Tp →₀ ℕ) (b : κ → Lw → K) (k : Φ ⊕ κ ⊕ Fin 2 → ℕ)
    (U : MvPowerSeries (Tp ⊕ Lw) K) :
    (∏ j, piece p Z Y aA dA aB dB b j ^ k j) * U =
      (∏ x, lowLin (b x) ^ k (Sum.inr (Sum.inl x))) *
        (MvPowerSeries.monomial (dTot dA dB k) (cTot p aA aB k) *
          (Z ^ k (Sum.inr (Sum.inr 0)) * (Y ^ k (Sum.inr (Sum.inr 1)) * U))) := by sorry
