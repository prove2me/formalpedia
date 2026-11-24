-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_LemOne_norm_coeff_mul_choose
-- name    : Formalism.InvariantFactorPaths.G7.LemOne.norm_coeff_mul_choose
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:54:43.059957+00:00
-- url     : https://prove2.me/theorems/ed8e0079-3be8-4b92-8fe3-e0fe14ba9d7f
-- title:
--   Lem One: norm coeff mul choose
-- statement:
--   The Lem One construction uses the norm coeff mul choose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/NotDvdChoosePowMul.lean#L195-L246
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/NotDvdChoosePowMul.lean#L195-L246

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

theorem Formalism.InvariantFactorPaths.G7.LemOne.norm_coeff_mul_choose {F : MvPowerSeries (Fin 2) K}
    (hF0 : MvPowerSeries.constantCoeff F = 0) (hFi : Integral F)
    (hF1 : ∀ n : Fin 2 →₀ ℕ, n.degree = 1 → MvPowerSeries.coeff n F = 1)
    {h : PowerSeries K} (hcob : Integral (cob F h)) {n : ℕ}
    (hlow : ∀ d < n, ‖PowerSeries.coeff d h‖ ≤ 1) {i : ℕ} (hi0 : 0 < i) (hin : i < n) :
    ‖PowerSeries.coeff n h * (n.choose i : K)‖ ≤ 1 := by sorry
