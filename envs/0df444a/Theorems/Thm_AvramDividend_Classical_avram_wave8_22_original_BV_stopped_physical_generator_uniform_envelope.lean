-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_stopped_physical_generator_uniform_envelope
-- name    : AvramDividend.Classical.avram_wave8_22_original_BV_stopped_physical_generator_uniform_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:25:50.225607+00:00
-- url     : https://prove2.me/theorems/119645ec-f3d6-4626-a56c-9b3bc3d390a9
-- title:
--   Original BV true stopped physical generator has explicit uniform envelope
-- statement:
--   For the unchanged original X and controlled left-limit reserve Y, the actual stopped generator F vanishes off A and equals the true discounted physical drift plus negative-jump ν integral minus q w on A. Uniform absolute bounds L, M, R on its three original components imply the same deterministic bound B=|drift|L+M+|q|R for every stopped point, including outside A.
-- source:
--   Exact accepted original single-time physical bound b5729ec5, original stopped indicator and controlled-reserve identity. Supplies uniform B for accepted source finite-clock HJB expectation theorem 20e052be.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_discounted_physical_generator_uniform_bound
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave8_22_original_BV_stopped_physical_generator_uniform_envelope {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
  (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ) (x : ℝ)
  (D : ℝ≥0 → Ω → ℝ) (A : Ω → Set ℝ≥0)
  (Y : (ℝ≥0 × Ω) → ℝ)
  (hY : ∀ p, Y p = Function.leftLim
    (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1)
  (K : ℝ≥0 → Ω → ℝ)
  (hK : ∀ p : ℝ≥0 × Ω, K p.1 p.2 =
    Real.exp (-(q * (p.1 : ℝ))) *
      (X.drift * deriv w (Y p) +
      (∫ z in Iio (0 : ℝ), w (Y p + z) - w (Y p) ∂X.ν) -
      q * w (Y p)))
  (F : (ℝ≥0 × Ω) → ℝ)
  (hF : ∀ p, F p = if p.1 ∈ A p.2 then K p.1 p.2 else 0)
  (L M R : ℝ) (hL : 0 ≤ L) (hM : 0 ≤ M) (hR : 0 ≤ R)
  (hBounds : ∀ p : ℝ≥0 × Ω, p.1 ∈ A p.2 →
    |deriv w (Y p)| ≤ L ∧
    |∫ z in Iio (0 : ℝ), w (Y p + z) - w (Y p) ∂X.ν| ≤ M ∧
    |w (Y p)| ≤ R) :
  0 ≤ |X.drift| * L + M + |q| * R ∧
  ∀ p : ℝ≥0 × Ω, ‖F p‖ ≤ |X.drift| * L + M + |q| * R := by sorry
