-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_ETerm_sum_piece
-- name    : Formalism.InvariantFactorPaths.G7.ETerm.sum_piece
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:30:25.826387+00:00
-- url     : https://prove2.me/theorems/7903b402-934f-4aa3-811e-d617a91d9b7b
-- title:
--   ETerm: sum piece
-- statement:
--   The ETerm construction uses the sum piece property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/NormNatCastLeOfDvd.lean#L327-L335
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/NormNatCastLeOfDvd.lean#L327-L335

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

theorem Formalism.InvariantFactorPaths.G7.ETerm.sum_piece (p : ℕ) (Z Y : MvPowerSeries (Tp ⊕ Lw) K) (aA : Φ → K) (dA : Φ → Tp →₀ ℕ)
    (aB : κ → K) (dB : κ → Tp →₀ ℕ) (b : κ → Lw → K) :
    ∑ j, piece p Z Y aA dA aB dB b j =
      ∑ φ, MvPowerSeries.C (aA φ) * topMonoS (Lw := Lw) (dA φ) +
        ∑ k, MvPowerSeries.C (aB k) * topMonoS (dB k) * lowLin (b k) + Z +
        MvPowerSeries.C (p : K) * Y := by sorry
