-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_lin_pow
-- name    : Formalism.InvariantFactorPaths.G7.TwoS.cg_lin_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:33:17.854874+00:00
-- url     : https://prove2.me/theorems/9536fbda-947d-47ab-abad-ac9480e56a5f
-- title:
--   Two S: cg lin pow
-- statement:
--   The Two S construction uses the cg lin pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/TheoremSFromKOneOf.lean#L276-L301
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/TheoremSFromKOneOf.lean#L276-L301

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_CyclicPowerClassOfExpEquiv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartB
import Definitions.Def_Lemmata_GeneralBFactRightExtra_Imports
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TheoremSFromKOneOf
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_low_subst_of_low
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_norm_finsum_le_of
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integralSubstV
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integral_mul
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integral_one
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integral_pow
import Theorems.Thm_Formalism_FG_SolveVAux_low_one_iff
import Theorems.Thm_Formalism_FG_SolveVAux_low_pow

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
open Formalism.DworkPowerSeriesWeights (Integral mvExp low_subst_of_low norm_finsum_le_of)
open Formalism.FG.SolveVAux (Low low_pow low_one_iff)
open Formalism.FG.IntegralSubstitution (integral_mul integral_pow integral_one integralSubstV)
open Formalism.InvariantFactorPaths.G7.TwoS
variable {K : Type} [NormedField K] [IsUltrametricDist K] {ν r0 r1 : ℕ}

theorem Formalism.InvariantFactorPaths.G7.TwoS.cg_lin_pow [NeZero ν] {p : ℕ} (hp : p.Prime) (hn : ‖(p : K)‖ = (p : ℝ)⁻¹)
    {w : ZMod (2 * ν) → K} (hw1 : ∀ s, ‖w s‖ ≤ 1)
    (hw2 : ∀ s, ‖w (s + 2) - w s ^ (p ^ 2)‖ ≤ (p : ℝ)⁻¹) (ab : Fin r0 × Fin r1) (l : ℕ) :
    Cg p (linW w ab ^ ((p ^ 2) ^ l))
      (∑ s : ZMod (2 * ν), MvPowerSeries.C (w (s + 2 * (l : ZMod (2 * ν)))) *
        (MvPowerSeries.X (s, ab) : MvPowerSeries (ZV ν r0 r1) K) ^ ((p ^ 2) ^ l)) := by sorry
