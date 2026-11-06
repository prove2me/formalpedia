-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_discounted_mixed_J_commutator_mesh_vanish
-- name    : AvramDividend.Classical.avram_p3_f2_original_discounted_mixed_J_commutator_mesh_vanish
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T23:12:06.143103+00:00
-- url     : https://prove2.me/theorems/d351eb24-00f3-4cf2-afdc-48eff9d26c91
-- title:
--   Original stopped BV physical-mesh discounted negative-J/Y mixed C1 error vanishes
-- statement:
--   For the original bounded-variation spectrally negative Lévy process, the true negative-jump raw cumulative J admits an almost-sure physical-grid total-variation telescope. If the mixed C1 Y/J source commutator has arbitrarily small per-cell error proportional to actual J increments along any refining stopped grid, then its entire exponentially discounted sum tends to zero almost surely. This supplies the mixed shift counterpart to the already Proved pure Y Taylor mesh-error convergence.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_raw_negative_J_grid_total_variation_exact
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_f2_original_discounted_mixed_J_commutator_mesh_vanish
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (q : ℝ) (hq : 0 ≤ q) :
    ∀ᵐ ω ∂P,
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω else 0
      let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
      ∀ (T : ℝ≥0) (u : ℕ → ℕ → ℝ≥0) (n : ℕ → ℕ),
        let z : ℕ → ℕ → ℝ := fun m i =>
          x + X.X (u m i) ω - rightLimit D (u m i) ω
        let c : ℕ → ℕ → ℝ := fun m i =>
          Y (u m (i + 1)) - Y (u m i)
        let j : ℕ → ℕ → ℝ := fun m i =>
          J (u m (i + 1)) - J (u m i)
        (∀ m, u m 0 = 0) →
        (∀ m, u m (n m) = T) →
        (∀ m i, i < n m → u m i ≤ u m (i + 1)) →
        (∀ ε : ℝ, 0 < ε →
          ∀ᶠ m in Filter.atTop, ∀ i, i < n m →
            |w (z m i + c m i - j m i) - w (z m i + c m i) -
              w (z m i - j m i) + w (z m i)| ≤ ε * |j m i|) →
        ∀ η : ℝ, 0 < η →
          ∀ᶠ m in Filter.atTop,
            |∑ i ∈ Finset.range (n m),
              Real.exp (-q * (u m i : ℝ)) *
                (w (z m i + c m i - j m i) - w (z m i + c m i) -
                  w (z m i - j m i) + w (z m i))| < η := by sorry
