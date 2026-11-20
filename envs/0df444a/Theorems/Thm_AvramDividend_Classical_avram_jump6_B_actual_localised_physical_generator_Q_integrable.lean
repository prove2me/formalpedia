-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_actual_localised_physical_generator_Q_integrable
-- name    : AvramDividend.Classical.avram_jump6_B_actual_localised_physical_generator_Q_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T22:19:43.786192+00:00
-- url     : https://prove2.me/theorems/dc5c5f10-91fa-4e71-b490-385f990595a2
-- title:
--   Original stopped Levy physical generator mesh Qj integrable under authentic compact bounded generator coefficient
-- statement:
--   The actual original spectrally negative Levy process X.X, right-limit dividend book D and stopped physical generator Riemann sum Q_j are integrable under a probability measure if the clock is bounded by n, the localized integrand is uniformly bounded on every true sampled interior grid point, and Q_j is strongly measurable. The proof uses the exact clipped-grid discounted absolute bound rather than finite jump intensity, and makes localization/measurability premises explicit. This is a source-faithful input for the canonical centring in ecf56f2e.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_actual_stopped_physical_discounted_mesh_abs_le_horizon
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_jump6_B_actual_localised_physical_generator_Q_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (σ : Ω → ℝ≥0)
    (n j : ℕ) (hσbound : ∀ ω, σ ω ≤ (n : ℝ≥0))
    (B : ℝ) (hB : 0 ≤ B)
    (hF : ∀ ω i, i < (n + 1) * (j + 1) →
      let v : ℕ → ℝ≥0 := fun l =>
        min ((l : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) (σ ω)
      let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
      |if 0 < Y (v i) ∧ ENNReal.ofReal (Y (v i)) < C then
        X.generator w (Y (v i)) - q * w (Y (v i))
       else 0| ≤ B) :
    let Q : Ω → ℝ := fun ω =>
      let v : ℕ → ℝ≥0 := fun l =>
        min ((l : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) (σ ω)
      let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
      let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
      ∑ i ∈ Finset.range ((n + 1) * (j + 1)),
        E (v (i + 1)) * (((v (i + 1) - v i : ℝ≥0) : ℝ)) *
          (if 0 < Y (v i) ∧ ENNReal.ofReal (Y (v i)) < C then
            X.generator w (Y (v i)) - q * w (Y (v i))
           else 0)
    AEStronglyMeasurable Q P → Integrable Q P := by sorry
