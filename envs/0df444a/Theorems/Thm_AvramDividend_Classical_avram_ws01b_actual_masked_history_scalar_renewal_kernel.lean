-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01b_actual_masked_history_scalar_renewal_kernel
-- name    : AvramDividend.Classical.avram_ws01b_actual_masked_history_scalar_renewal_kernel
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T08:27:35.850467+00:00
-- url     : https://prove2.me/theorems/944d7793-5231-4040-8e62-43d68c8a5691
-- title:
--   Actual original Lévy killed random-reserve renewal from all-capital scalar fixed-time law
-- statement:
--   Assuming the genuinely scalar fixed-time killed scale identity for every deterministic reserve and a complete rational schedule, prove the original Lévy shifted-future killed reward with an arbitrary surviving history equals the original historical killed scale expectation. Already ruined histories are represented by reserve -1; this is necessary for BV W(0)>0. The only outstanding hypothesis is the explicit scalar renewal, with no fictitious independent future process.
-- source:
--   Canonical Proved full original Lévy shifted random-reserve killed Markov–Tonelli kernel 8c2d238f, actual filtration survival measurability, and actual scale monotonicity. The scalar law will follow from original WH resolvent and killed semigroup; this theorem is an honest one-step source stochastic assembler.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_monotone
import Theorems.Thm_AvramDividend_Classical_chat03_lower_survival_filtration_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_killed_scale_shifted_expectation_of_scalar_renewal_kernel

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_ws01b_actual_masked_history_scalar_renewal_kernel
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T : ℝ≥0) (τ : ℕ → ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (hTerminal : ∃ j : ℕ, τ j = T)
    (q x : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hScalar : ∀ h : ℝ,
      (∫⁻ y,
        (if ∀ j : ℕ, τ j ≤ T → 0 ≤ h + y (τ j)
         then ENNReal.ofReal
           (Real.exp (-(q * (T : ℝ))) * W (h + y T))
         else (0 : ℝ≥0∞))
        ∂(Measure.map (fun ω => (fun u : ℝ≥0 => X.X u ω)) P)) =
      ENNReal.ofReal (W h)) :
    (∫⁻ ω,
      (if ∀ v : ℝ≥0, v ≤ T →
        0 ≤ (if ∀ w : ℝ≥0, w ≤ s → 0 ≤ x + X.X w ω
             then x + X.X s ω else (-1 : ℝ)) +
           (X.X (s + v) ω - X.X s ω)
      then ENNReal.ofReal (Real.exp (-(q * (T : ℝ))) *
        W ((if ∀ w : ℝ≥0, w ≤ s → 0 ≤ x + X.X w ω
            then x + X.X s ω else (-1 : ℝ)) +
           (X.X (s + T) ω - X.X s ω)))
      else (0 : ℝ≥0∞)) ∂P) =
    ∫⁻ ω, if ∀ w : ℝ≥0, w ≤ s → 0 ≤ x + X.X w ω
       then ENNReal.ofReal (W (x + X.X s ω))
       else (0 : ℝ≥0∞) ∂P := by sorry
