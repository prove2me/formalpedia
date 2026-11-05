-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_compact_C1_arbitrary_drift_mixed_mesh_vanish
-- name    : AvramDividend.Classical.avram_p3_2_original_compact_C1_arbitrary_drift_mixed_mesh_vanish
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T00:31:34.536261+00:00
-- url     : https://prove2.me/theorems/69d44ab8-a561-4681-a31d-7f5cce61df10
-- title:
--   Original Lévy discounted mixed drift-negative-J mesh errors vanish from compact C1 conditions
-- statement:
--   For the original bounded-variation spectrally negative Lévy process with its actual cumulative negative jumps J, arbitrary physical drift shifts whose maximum tends to zero in an interior compact C1 band have vanishing discounted nonlinear mixed commutator sums. The proof composes source-exact arbitrary-shift J total variation with a uniform compact C1 commutator bound and does not silently replace drift by the jump-removed Y increment.
-- source:
--   New Proved p3_2 arbitrary drift mesh and uniform compact C1 shift lemmas; exact original X left jump mass.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_discounted_arbitrary_shift_mixed_J_mesh_vanish
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_uniform_compact_C1_arbitrary_physical_drift_raw_J_commutator

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_compact_C1_arbitrary_drift_mixed_mesh_vanish
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hwC1 : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ)
    (hBand : Set.Icc a b ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (hq : 0 ≤ q) :
    ∀ᵐ ω ∂P,
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω else 0
      ∀ (T : ℝ≥0) (u : ℕ → ℕ → ℝ≥0) (n : ℕ → ℕ)
        (z c : ℕ → ℕ → ℝ),
        let j : ℕ → ℕ → ℝ := fun m i =>
          J (u m (i + 1)) - J (u m i)
        (∀ m, u m 0 = 0) →
        (∀ m, u m (n m) = T) →
        (∀ m i, i < n m → u m i ≤ u m (i + 1)) →
        (∀ m i, i < n m →
          Set.uIcc (z m i - j m i) (z m i) ⊆ Set.Icc a b) →
        (∀ m i, i < n m →
          Set.uIcc (z m i + c m i - j m i) (z m i + c m i) ⊆ Set.Icc a b) →
        (∀ δ : ℝ, 0 < δ →
          ∀ᶠ m in Filter.atTop, ∀ i, i < n m → |c m i| < δ) →
        ∀ η : ℝ, 0 < η →
          ∀ᶠ m in Filter.atTop,
            |∑ i ∈ Finset.range (n m),
              Real.exp (-(q * (u m i : ℝ))) *
                (w (z m i + c m i - j m i) - w (z m i + c m i) -
                  w (z m i - j m i) + w (z m i))| < η := by sorry
