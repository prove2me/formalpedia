-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_low_PhiH
-- name    : Formalism.InvariantFactorPaths.G7.DworkIntegrality.low_PhiH
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:25:29.728816+00:00
-- url     : https://prove2.me/theorems/153b603b-4e72-4c94-9589-ea76b02d6655
-- title:
--   Dwork Integrality: low Phi H
-- statement:
--   The Dwork Integrality construction uses the low Phi H property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/LocalComponentGL.lean#L168-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/LocalComponentGL.lean#L168-L178

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
variable {K ι : Type} [Field K]

theorem Formalism.InvariantFactorPaths.G7.DworkIntegrality.low_PhiH {p : ℕ} (hp : p ≠ 0) (σ : K →+* K) {d : ℕ} {h : MvPowerSeries ι K}
    (hh : Low d h) : Low (p * d) (PhiH hp σ h) := by sorry
