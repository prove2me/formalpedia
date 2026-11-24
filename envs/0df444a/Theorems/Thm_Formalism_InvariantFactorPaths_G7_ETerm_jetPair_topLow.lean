-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_ETerm_jetPair_topLow
-- name    : Formalism.InvariantFactorPaths.G7.ETerm.jetPair_topLow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:27:04.422669+00:00
-- url     : https://prove2.me/theorems/9a6863a8-ff00-460a-97d2-851c275954a2
-- title:
--   ETerm: jet Pair top Low
-- statement:
--   The ETerm construction uses the jet Pair top Low property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/NormNatCastLeOfDvd.lean#L104-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/NormNatCastLeOfDvd.lean#L104-L112

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
variable {K Tp Lw : Type} [Field K]

theorem Formalism.InvariantFactorPaths.G7.ETerm.jetPair_topLow [Fintype Tp] [Fintype Lw] (e : Tp →₀ ℕ)
    (R : MvPolynomial Lw K) (G : MvPowerSeries (Tp ⊕ Lw) K) :
    jetPair (topMonoP e * lowPoly R) G =
      ∑ n ∈ R.support, MvPolynomial.coeff n R * ((mfact e * mfact n : ℕ) : K) *
        MvPowerSeries.coeff (jn e n) G := by sorry
