-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_CoefficientSupportCongruences_scale_of_suppOK
-- name    : Formalism.InvariantFactorPaths.G7.CoefficientSupportCongruences.scale_of_suppOK
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T10:21:54.133366+00:00
-- url     : https://prove2.me/theorems/f465decf-621b-4b88-bc2e-dae05d656c07
-- title:
--   Coefficient Support Congruences: scale of supp OK
-- statement:
--   The Coefficient Support Congruences construction uses the scale of supp OK property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/FrobeniusPartialCoboundaryBound.lean#L106-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/FrobeniusPartialCoboundaryBound.lean#L106-L128

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_ThmSUniform
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_FrobeniusPartialCoboundaryBound
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_PhiH_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_C
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_add
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_neg
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_sub
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_frob_congr
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_int_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_int_pow

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
open DworkIntegrality (Bd bd_add bd_sub bd_neg bd_mul bd_C int_mul int_pow frob_congr PhiH PhiH_apply)
open Formalism.InvariantFactorPaths.G7.CoefficientSupportCongruences
open FrobeniusSubstitution
variable {K : Type} [Field K]

theorem Formalism.InvariantFactorPaths.G7.CoefficientSupportCongruences.scale_of_suppOK {p : ℕ} {G : MvPowerSeries (Fin 2) K} (hG : SuppOK p G) {ζ : K}
    (hζ : ζ ^ (p ^ 2 - 1) = 1) :
    MvPowerSeries.subst ![MvPowerSeries.C ζ * (MvPowerSeries.X 0 :
        MvPowerSeries (Fin 2) K), MvPowerSeries.X 1] G =
      MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K),
        MvPowerSeries.C (ζ ^ p) * MvPowerSeries.X 1] G := by sorry
