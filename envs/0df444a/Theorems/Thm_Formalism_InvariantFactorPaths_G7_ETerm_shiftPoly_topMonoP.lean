-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_ETerm_shiftPoly_topMonoP
-- name    : Formalism.InvariantFactorPaths.G7.ETerm.shiftPoly_topMonoP
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:27:34.125852+00:00
-- url     : https://prove2.me/theorems/35c50dd5-7aea-4d16-9fec-bdc26ac3149b
-- title:
--   ETerm: shift Poly top Mono P
-- statement:
--   The ETerm construction uses the shift Poly top Mono P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/NormNatCastLeOfDvd.lean#L130-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/NormNatCastLeOfDvd.lean#L130-L135

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
variable {κ : Type} [Fintype κ]

theorem Formalism.InvariantFactorPaths.G7.ETerm.shiftPoly_topMonoP (b : κ → Lw → K) (e : Tp →₀ ℕ) :
    shiftPoly (ext0 (Tp := Tp) b) (topMonoP e) = MvPolynomial.C (topMonoP e) := by sorry
