-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_frob_finset
-- name    : Formalism.InvariantFactorPaths.G7.DworkIntegrality.frob_finset
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:26:25.570878+00:00
-- url     : https://prove2.me/theorems/2a311cb8-5fa3-4116-8aee-c980f242e46c
-- title:
--   Dwork Integrality: frob finset
-- statement:
--   The Dwork Integrality construction uses the frob finset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/LocalComponentGL.lean#L217-L237
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/LocalComponentGL.lean#L217-L237

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
variable {K ι : Type} [NormedField K] [IsUltrametricDist K] {p : ℕ} {σ : K →+* K}

theorem Formalism.InvariantFactorPaths.G7.DworkIntegrality.frob_finset (hp : p.Prime) (hnp : ‖(p : K)‖ = (p : ℝ)⁻¹)
    (hσ : ∀ a : K, ‖a‖ ≤ 1 → ‖σ a - a ^ p‖ ≤ (p : ℝ)⁻¹) (c : (ι →₀ ℕ) → K) (hc : ∀ m, ‖c m‖ ≤ 1)
    (s : Finset (ι →₀ ℕ)) :
    Bd 1 (∑ m ∈ s, MvPowerSeries.monomial m (c m)) ∧
    Bd (p : ℝ)⁻¹ ((∑ m ∈ s, MvPowerSeries.monomial m (c m)) ^ p -
      PhiH hp.ne_zero σ (∑ m ∈ s, MvPowerSeries.monomial m (c m))) := by sorry
