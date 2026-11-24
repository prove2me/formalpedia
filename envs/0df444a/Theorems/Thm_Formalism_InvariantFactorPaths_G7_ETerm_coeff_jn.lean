-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_ETerm_coeff_jn
-- name    : Formalism.InvariantFactorPaths.G7.ETerm.coeff_jn
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:27:32.194425+00:00
-- url     : https://prove2.me/theorems/5419b25c-0aed-43be-b860-9630d830339c
-- title:
--   ETerm: coeff jn
-- statement:
--   The ETerm construction uses the coeff jn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/NormNatCastLeOfDvd.lean#L78-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/NormNatCastLeOfDvd.lean#L78-L82

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

theorem Formalism.InvariantFactorPaths.G7.ETerm.coeff_jn (e : Tp →₀ ℕ) (n : Lw →₀ ℕ) (R : MvPolynomial Lw K) :
    MvPolynomial.coeff (jn e n) (topMonoP e * lowPoly R) = MvPolynomial.coeff n R := by sorry
