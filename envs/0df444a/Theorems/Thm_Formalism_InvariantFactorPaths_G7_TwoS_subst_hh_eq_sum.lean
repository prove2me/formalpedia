-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_subst_hh_eq_sum
-- name    : Formalism.InvariantFactorPaths.G7.TwoS.subst_hh_eq_sum
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:28:25.216658+00:00
-- url     : https://prove2.me/theorems/1eb61bb8-972a-48c0-8548-aa53ff699de9
-- title:
--   Two S: subst hh eq sum
-- statement:
--   The Two S construction uses the subst hh eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/TheoremSFromKOneOf.lean#L507-L515
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/TheoremSFromKOneOf.lean#L507-L515

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
variable {K : Type} [NormedField K] [IsUltrametricDist K] {ν r0 r1 : ℕ} [NeZero ν]

theorem Formalism.InvariantFactorPaths.G7.TwoS.subst_hh_eq_sum {τ E : Type} [Fintype E] (p : ℕ) (c c' : K)
    {φ : Bool × E → MvPowerSeries τ K} (hs : MvPowerSeries.HasSubst φ) :
    MvPowerSeries.subst φ (hh1 (E := E) p c c') =
      ∑ e : E, (MvPowerSeries.C c * φ (false, e) * φ (true, e) ^ p -
        MvPowerSeries.C c' * φ (false, e) ^ p * φ (true, e)) := by sorry
