-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_small_of_exp
-- name    : Formalism.InvariantFactorPaths.G7.DworkIntegrality.small_of_exp
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:26:31.481599+00:00
-- url     : https://prove2.me/theorems/6dcacb43-b2d7-4205-b5df-b26b9f472956
-- title:
--   Dwork Integrality: small of exp
-- statement:
--   The Dwork Integrality construction uses the small of exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/LocalComponentGL.lean#L329-L360
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/LocalComponentGL.lean#L329-L360

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_CyclicPowerClassOfExpEquiv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartB
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LocalComponentGL
import Theorems.Thm_Formalism_FG_SolveVAux_low_add
import Theorems.Thm_Formalism_FG_SolveVAux_low_mono
import Theorems.Thm_Formalism_FG_SolveVAux_low_mul
import Theorems.Thm_Formalism_FG_SolveVAux_low_neg
import Theorems.Thm_Formalism_FG_SolveVAux_low_one_iff
import Theorems.Thm_Formalism_FG_SolveVAux_low_pow
import Theorems.Thm_Formalism_FG_SolveVAux_low_sub
import Theorems.Thm_Formalism_FG_SolveVAux_low_zero

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
open Formalism.FG.SolveVAux (Low low_zero low_mono low_add low_sub low_neg low_mul low_pow low_one_iff)
open Formalism.InvariantFactorPaths.G7.DworkIntegrality
variable {K ι : Type} [NormedField K] [CharZero K]
variable [IsUltrametricDist K] {p : ℕ}

theorem Formalism.InvariantFactorPaths.G7.DworkIntegrality.small_of_exp [Finite ι] (hp : p.Prime) (hnp : ‖(p : K)‖ = (p : ℝ)⁻¹)
    {D : MvPowerSeries ι K} (hD0 : MvPowerSeries.constantCoeff D = 0)
    (hD : Bd (p : ℝ)⁻¹ (mvExp D - 1)) : Bd (p : ℝ)⁻¹ D := by sorry
