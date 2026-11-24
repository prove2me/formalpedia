-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_LemOne_norm_coeff_of_pow
-- name    : Formalism.InvariantFactorPaths.G7.LemOne.norm_coeff_of_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:54:38.243304+00:00
-- url     : https://prove2.me/theorems/2c08f874-c3e7-42cc-94c8-d40b527f8f21
-- title:
--   Lem One: norm coeff of pow
-- statement:
--   The Lem One construction uses the norm coeff of pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/NotDvdChoosePowMul.lean#L264-L274
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/NotDvdChoosePowMul.lean#L264-L274

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_NotDvdChoosePowMul
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
open Formalism.InvariantFactorPaths.G7.LemOne
variable {K : Type} [NormedField K] [IsUltrametricDist K]

theorem Formalism.InvariantFactorPaths.G7.LemOne.norm_coeff_of_pow {p : ℕ} (hp : p.Prime) (hnp : ‖(p : K)‖ = (p : ℝ)⁻¹)
    {F : MvPowerSeries (Fin 2) K}
    (hF0 : MvPowerSeries.constantCoeff F = 0) (hFi : Integral F)
    (hF1 : ∀ n : Fin 2 →₀ ℕ, n.degree = 1 → MvPowerSeries.coeff n F = 1)
    {h : PowerSeries K} (hcob : Integral (cob F h)) (k : ℕ)
    (hlow : ∀ d < p ^ (k + 1), ‖PowerSeries.coeff d h‖ ≤ 1) :
    ‖(p : K) * PowerSeries.coeff (p ^ (k + 1)) h‖ ≤ 1 := by sorry
