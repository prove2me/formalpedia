-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_03_sourceLevy_theta_dyadic_expected_mesh_eq_stieltjes_grid
-- name    : AvramDividend.Classical.avram_wave4_03_sourceLevy_theta_dyadic_expected_mesh_eq_stieltjes_grid
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T00:23:59.039347+00:00
-- url     : https://prove2.me/theorems/72cb64d8-1afc-43a4-9edf-fb5fd321def1
-- title:
--   Exact dyadic theta-exponential Stieltjes mesh equals original random-dividend-measure finite cells
-- statement:
--   For original Lévy X, the very same control D and any exponential tilt theta, the full random-measure Stieltjes upper-dyadic mesh integral equals the sum of its exact finite time-cell Stieltjes integrals in expectation. No jump-only approximation, atom concentration, or independent replacement process. Algebraically uses the proved exact all-real right dyadic time-cell equality.
-- source:
--   Existing all-real dyadic step identity 3f4cb787; no probabilistic assumptions beyond the source-process notation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_rightDyadic_allRealIoc_step_eq_ceiling
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_03_sourceLevy_theta_dyadic_expected_mesh_eq_stieltjes_grid
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (θ : ℝ)
    (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    (∫⁻ ω, ∫⁻ s : ℝ,
      if s ∈ Ioc (0 : ℝ) (T : ℝ) then
        let k := Nat.ceil (((s.toNNReal / T : ℝ≥0) : ℝ) * (2 : ℝ) ^ n)
        let u := ((k : ℝ≥0) / (2 : ℝ≥0) ^ n) * T
        ENNReal.ofReal (θ * Real.exp (θ *
          (X.X u ω - rightLimit D u ω) - (u : ℝ) * X.ψ θ))
      else 0 ∂dividendMeasure D ω ∂P) =
    (∫⁻ ω, ∫⁻ s : ℝ,
      ∑ i ∈ Finset.range (2 ^ n),
        if s ∈ Ioc (((i : ℝ≥0) / (2 : ℝ≥0) ^ n) * T : ℝ)
            ((((i + 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n) * T : ℝ) then
          ENNReal.ofReal (θ * Real.exp (θ *
            (X.X ((((i + 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n) * T) ω -
              rightLimit D ((((i + 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n) * T) ω) -
            (((((i + 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n) * T) : ℝ) * X.ψ θ))
        else 0 ∂dividendMeasure D ω ∂P) := by sorry
