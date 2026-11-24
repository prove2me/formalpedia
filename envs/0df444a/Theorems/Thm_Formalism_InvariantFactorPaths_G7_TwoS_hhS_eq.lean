-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_hhS_eq
-- name    : Formalism.InvariantFactorPaths.G7.TwoS.hhS_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:33:13.784803+00:00
-- url     : https://prove2.me/theorems/0d25bed5-15de-4a13-b430-24f4c8a2ecfa
-- title:
--   Two S: hh S eq
-- statement:
--   The Two S construction uses the hh S eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/TheoremSFromKOneOf.lean#L517-L569
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/TheoremSFromKOneOf.lean#L517-L569

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

theorem Formalism.InvariantFactorPaths.G7.TwoS.hhS_eq {p : ℕ} {om oms : Fin ν → ZMod (2 * ν) → K}
    (hO3 : ∀ a b : ZMod (2 * ν), a.val % 2 = b.val % 2 →
      ∑ r, oms r a * om r b = if a = b then 1 else 0) (c c' : K) :
    hhS (r0 := r0) (r1 := r1) p (uS c c') =
      ∑ e : EV ν r0 r1,
        (MvPowerSeries.C c * posW p (wE (oms e.1) 0) e.2 * posW' p (wE' (om e.1) 1) e.2 -
          MvPowerSeries.C c' * posW' p (wE' (oms e.1) 0) e.2 * posW p (wE (om e.1) 1) e.2) := by sorry
