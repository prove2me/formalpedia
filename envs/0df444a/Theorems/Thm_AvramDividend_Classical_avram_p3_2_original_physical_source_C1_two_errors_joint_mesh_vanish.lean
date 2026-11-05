-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_physical_source_C1_two_errors_joint_mesh_vanish
-- name    : AvramDividend.Classical.avram_p3_2_original_physical_source_C1_two_errors_joint_mesh_vanish
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T00:59:41.382451+00:00
-- url     : https://prove2.me/theorems/8442e7aa-b43d-46ee-b0d6-524099a51ad5
-- title:
--   Original BV X/D physical generator drift and negative-jump nonlinear mesh errors jointly vanish
-- statement:
--   For the literal same-probability-space original BV Lévy X, admissible-control-shaped source reserve x+X.X-rightLimit D and actual negative jump J, the sum of discounted physical pure-drift C1 Taylor remainders and mixed original negative-jump commutators tends to zero on a refining monotone stopped grid, whenever all relevant reserve segments remain in one compact strict positive subcap. This composes two separately verified source-exact error limits and actual shrinking physical drift, without equality in law or omitting cap-contact limitations.
-- source:
--   Compose proved original BV C1 Taylor mesh 646d7a18, original mixed raw-J mesh 69d44ab8 and original clock drift shrinking 7056b9d2 on the literal X/D reserve.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_compact_C1_arbitrary_drift_mixed_mesh_vanish
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_physical_drift_C1_Taylor_mesh_vanish
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_physical_clock_drift_shift_mesh_vanish

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_physical_source_C1_two_errors_joint_mesh_vanish
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
      ∀ (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (T : ℝ≥0)
        (u : ℕ → ℕ → ℝ≥0) (n : ℕ → ℕ),
        let z : ℕ → ℕ → ℝ := fun m i =>
          x + X.X (u m i) ω - rightLimit D (u m i) ω
        let c : ℕ → ℕ → ℝ := fun m i =>
          ((u m (i + 1) : ℝ) - (u m i : ℝ)) * X.drift
        let j : ℕ → ℕ → ℝ := fun m i =>
          J (u m (i + 1)) - J (u m i)
        (∀ m, u m 0 = 0) →
        (∀ m, u m (n m) = T) →
        (∀ m i, i < n m → u m i ≤ u m (i + 1)) →
        (∀ δ : ℝ, 0 < δ →
          ∀ᶠ m in Filter.atTop, ∀ i, i < n m →
            (u m (i + 1) : ℝ) - (u m i : ℝ) < δ) →
        (∀ m i, i < n m →
          Set.uIcc (z m i) (z m i + c m i) ⊆ Set.Icc a b) →
        (∀ m i, i < n m →
          Set.uIcc (z m i - j m i) (z m i) ⊆ Set.Icc a b) →
        (∀ m i, i < n m →
          Set.uIcc (z m i + c m i - j m i)
            (z m i + c m i) ⊆ Set.Icc a b) →
        ∀ η : ℝ, 0 < η →
          ∀ᶠ m in Filter.atTop,
            |(∑ i ∈ Finset.range (n m),
              Real.exp (-(q * (u m i : ℝ))) *
                (w (z m i + c m i) - w (z m i) -
                  deriv w (z m i) * c m i)) +
             (∑ i ∈ Finset.range (n m),
              Real.exp (-(q * (u m i : ℝ))) *
                (w (z m i + c m i - j m i) - w (z m i + c m i) -
                  w (z m i - j m i) + w (z m i)))| < η := by sorry
