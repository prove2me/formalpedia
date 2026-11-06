-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_bounded_stop_negative_band_marked_sum_L1
-- name    : AvramDividend.Classical.avram_p4_s3_original_bounded_stop_negative_band_marked_sum_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T12:22:08.219915+00:00
-- url     : https://prove2.me/theorems/8fdaf193-2beb-4dd6-b14a-9d98a5e4c63b
-- title:
--   Original stopped finite negative-band marked-jump sum has L1 bound by physical Levy compensator intensity
-- statement:
--   For the literal original Lévy path and an exact finite enumeration F of negative-band jump times before a sample-dependent τ≤T, every measurable finite sum of uniformly bounded state-dependent jump coefficients is integrable and its expected absolute value is at most the coefficient bound times the exact physical intensity Tν(Band). This gives a source-faithful L1 control for actual stopped marked jump sums and complements the predictable mean-zero theorem.
-- source:
--   Combine the Proved true bounded stopped count first moment 5e515f36 with exact finset identification, finite-sum triangle inequality and |H(u,ω)|≤B; dominate the physical marked source sum by B*Kτ pointwise and integrate.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_bounded_stop_negative_band_count_L1_first_moment
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_s3_original_bounded_stop_negative_band_marked_sum_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ)
    (τ : Ω → ℝ≥0) (hτ : ∀ ω, τ ω ≤ T)
    (F : Ω → Finset ℝ≥0)
    (hF : ∀ ω, (↑(F ω) : Set ℝ≥0) = {u : ℝ≥0 | 0 < u ∧ u ≤ τ ω ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((n : ℝ) + 1))})
    (hKmeas : Measurable (fun ω : Ω => {u : ℝ≥0 | 0 < u ∧ u ≤ τ ω ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((n : ℝ) + 1))}.ncard))
    (H : ℝ≥0 → Ω → ℝ)
    (hSumMeas : Measurable (fun ω => (F ω).sum (fun u => H u ω)))
    (B : ℝ) (hB : 0 ≤ B) (hH : ∀ u ω, |H u ω| ≤ B) :
    let r : ℝ :=
      ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
    Integrable (fun ω => (F ω).sum (fun u => H u ω)) P ∧
    (∫ ω, |(F ω).sum (fun u => H u ω)| ∂P) ≤ B * r := by sorry
