-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_LemOne_correct
-- name    : Formalism.InvariantFactorPaths.G7.LemOne.correct
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:32:56.502248+00:00
-- url     : https://prove2.me/theorems/245cfdc7-7fab-47e9-a606-5dff1912a05f
-- title:
--   Lem One: correct
-- statement:
--   The Lem One construction uses the correct property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/NotDvdChoosePowMul.lean#L297-L326
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/NotDvdChoosePowMul.lean#L297-L326

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

theorem Formalism.InvariantFactorPaths.G7.LemOne.correct {p : ℕ} (hp : p.Prime) (hnp : ‖(p : K)‖ = (p : ℝ)⁻¹)
    {F : MvPowerSeries (Fin 2) K}
    (hF0 : MvPowerSeries.constantCoeff F = 0) (hFi : Integral F)
    (hF1 : ∀ n : Fin 2 →₀ ℕ, n.degree = 1 → MvPowerSeries.coeff n F = 1)
    {h g h' : PowerSeries K} (hcob : Integral (cob F h)) (k j : ℕ)
    (hlow : ∀ d < p ^ (k + 1), ‖PowerSeries.coeff d h‖ ≤ 1)
    (hglow : ∀ d < p ^ (k + 1), ‖(p : K) ^ j * PowerSeries.coeff d g‖ ≤ 1)
    (hgtop : PowerSeries.coeff (p ^ (k + 1)) g = ((p : K) ^ (j + 1))⁻¹)
    (hh' : h' = h - PowerSeries.C ((p : K) * PowerSeries.coeff (p ^ (k + 1)) h * (p : K) ^ j) * g)
    (hcob' : Integral (cob F h')) :
    ‖(p : K) * PowerSeries.coeff (p ^ (k + 1)) h‖ ≤ 1 ∧
      ∀ d < p ^ (k + 2), ‖PowerSeries.coeff d h'‖ ≤ 1 := by sorry
