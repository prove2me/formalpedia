-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24_original_stopped_bounded_predictable_smallmark_grid_common_integrable_envelope
-- name    : AvramDividend.Classical.avram_b24_original_stopped_bounded_predictable_smallmark_grid_common_integrable_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T19:49:40.15581+00:00
-- url     : https://prove2.me/theorems/8c04d03c-df41-4365-909d-f6aeebad8eec
-- title:
--   All actual original stopped compensated smallmark bounded predictable chronological grid gains share one integrable Poisson count envelope independent of grid refinement
-- statement:
--   For a true original finite-negative-activity Lévy source X with arbitrary same-space intrinsic Jsmall residual witness, every bounded real predictable source weight system W_i with uniform bound L over any original monotone chronological physical grid clipped at any actual random ruin/stopping clock σ yields a compensated marked gain whose absolute value is dominated by exactly L times the same original integrable finite-horizon negative marked Poisson count plus genuine signed compensator drift B_T, independent of the number of cells and all grid refinements. The proof uses the original same-source pathwise uniform TOTAL VARIATION bound for the physically stopped Jsmall grid, finite norm triangle, multiplication norm and the coefficient bound L. Integrability of the common majorant L B_T follows from its genuine marked Poisson count first moment, without assumptions on large negative mark second moments, zero ν, synthetic noise or postruin reserve. This directly isolates the B219 required BJ random integrable source majorant for a uniformly bounded marked predictable coefficient family; existence of such uniform coefficient bounds and the original C2 discounted cash ledger remain explicit separate obligations.
-- source:
--   B24 original all true ruin-clipped chronological smallmark grid integrable uniform variation, finite sum norm and bounded coefficients.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b24_original_stopped_bounded_predictable_smallmark_grid_common_integrable_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (Jsmall : ℝ≥0 → Ω → ℝ)
    (hJsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω)
        atTop (𝓝 (Jsmall t ω)))
    (T : ℝ≥0) (L : ℝ) (hL : 0 ≤ L) :
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Ioo (-1 : ℝ) 0)
    let B : Ω → ℝ := fun ω => (N ω).toReal +
      (T : ℝ) * ‖∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν‖
    Integrable (fun ω => L * B ω) P ∧
      ∀ᵐ ω ∂P, ∀ (n : ℕ) (t : ℕ → ℝ≥0)
        (σ : Ω → ℝ≥0) (W : ℕ → Ω → ℝ),
        Monotone t → t n ≤ T →
        (∀ i ∈ Finset.range n, ∀ ω', ‖W i ω'‖ ≤ L) →
        ‖∑ i ∈ Finset.range n, W i ω *
          (Jsmall (min (t (i + 1)) (σ ω)) ω -
            Jsmall (min (t i) (σ ω)) ω)‖ ≤ L * B ω := by sorry
