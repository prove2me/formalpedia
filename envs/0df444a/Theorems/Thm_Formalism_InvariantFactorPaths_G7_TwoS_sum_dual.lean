-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_sum_dual
-- name    : Formalism.InvariantFactorPaths.G7.TwoS.sum_dual
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:28:37.514467+00:00
-- url     : https://prove2.me/theorems/f2e3f050-896b-4d17-93b3-1831d2abc293
-- title:
--   Two S: sum dual
-- statement:
--   The Two S construction uses the sum dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/TheoremSFromKOneOf.lean#L427-L458
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/TheoremSFromKOneOf.lean#L427-L458

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

theorem Formalism.InvariantFactorPaths.G7.TwoS.sum_dual {K ι : Type} [Field K] {ν r0 r1 : ℕ} [NeZero ν] (a b : Fin ν → ZMod (2 * ν) → K)
    (par : ZMod (2 * ν) → Prop) [DecidablePred par]
    (h : ∀ s s', ∑ r, a r s * b r s' = if par s' ∧ s = s' + 1 then 1 else 0)
    (P Q : ZMod (2 * ν) → Fin r0 × Fin r1 → MvPowerSeries ι K) :
    ∑ e : EV ν r0 r1, (∑ s, MvPowerSeries.C (a e.1 s) * P s e.2) *
        (∑ s', MvPowerSeries.C (b e.1 s') * Q s' e.2) =
      ∑ s', if par s' then ∑ ab, Q s' ab * P (s' + 1) ab else 0 := by sorry
