-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_FrobeniusSubstitution_pderiv_prod
-- name    : Formalism.InvariantFactorPaths.G7.FrobeniusSubstitution.pderiv_prod
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:11:42.776906+00:00
-- url     : https://prove2.me/theorems/3eab43d5-ed8d-4ad0-b374-49e3d4f4bed0
-- title:
--   Frobenius Substitution: pderiv prod
-- statement:
--   The Frobenius Substitution construction uses the pderiv prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/PartialCoboundaryLinear.lean#L167-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/PartialCoboundaryLinear.lean#L167-L176

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LocalComponentGL
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LogarithmEquivalence
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_PartialCoboundaryLinear
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
open Formalism.InvariantFactorPaths.G7.FrobeniusSubstitution
variable {K : Type} [Field K]

theorem Formalism.InvariantFactorPaths.G7.FrobeniusSubstitution.pderiv_prod (k : K) (f g : PowerSeries K) :
    MvPowerSeries.pderiv K (0 : Fin 2) (MvPowerSeries.C k * (at1 0 f * at1 1 g)) =
      MvPowerSeries.C k * (at1 0 (PowerSeries.derivative K f) * at1 1 g) := by sorry
