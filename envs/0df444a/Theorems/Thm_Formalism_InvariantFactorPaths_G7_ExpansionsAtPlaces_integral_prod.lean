-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_ExpansionsAtPlaces_integral_prod
-- name    : Formalism.InvariantFactorPaths.G7.ExpansionsAtPlaces.integral_prod
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:43:48.274715+00:00
-- url     : https://prove2.me/theorems/819a534f-276a-4e03-b180-ce8274ac198c
-- title:
--   Expansions At Places: integral prod
-- statement:
--   The Expansions At Places construction uses the integral prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/ExpansionsAtPlaces.lean#L35-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/ExpansionsAtPlaces.lean#L35-L38

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_ThmSUniform
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EDecomp
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_MPlaces
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_ExpansionsAtPlaces
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integralSubstV
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integral_mul
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integral_one
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integral_pow
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_add
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_of_eq
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_pow
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_refl
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_sum
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_symm
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_trans
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_constantCoeff_sSub
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_integral_C
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_integral_X
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_integral_add
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_integral_neg
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_integral_sSub
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_integral_sum
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_integral_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_pinv_le_one

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
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.FG.SolveVAux (Low)
open Formalism.FG.IntegralSubstitution (integral_mul integral_pow integral_one integralSubstV)
open TwoS (Cg cg_refl cg_of_eq cg_symm cg_trans cg_add cg_sum cg_mul cg_pow
  integral_add integral_neg integral_sum integral_C integral_X integral_zero pinv_le_one
  constantCoeff_sSub integral_sSub)
open Formalism.InvariantFactorPaths.G7.ExpansionsAtPlaces

theorem Formalism.InvariantFactorPaths.G7.ExpansionsAtPlaces.integral_prod {K ι α : Type} [NormedField K] [IsUltrametricDist K] (s : Finset α)
    (x : α → MvPowerSeries ι K) (hx : ∀ i, Integral (x i)) : Integral (∏ i ∈ s, x i) := by sorry
