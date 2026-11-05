-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_discounted_arbitrary_shift_mixed_J_mesh_vanish
-- name    : AvramDividend.Classical.avram_p3_2_original_discounted_arbitrary_shift_mixed_J_mesh_vanish
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T00:23:32.199363+00:00
-- url     : https://prove2.me/theorems/bfb7000f-fbd7-4897-a5ed-62a65a5b934c
-- title:
--   Original BV discounted mixed negative-J mesh errors vanish for arbitrary physical drift shifts
-- statement:
--   For any original BV Lévy path and physical monotone partitions from 0 to T, the actual negative-jump J total variation controls arbitrary drift-shifted discounted nonlinear commutator errors. An eventually arbitrarily small cellwise ε|ΔJ| bound implies the entire weighted mixed error tends to zero. The arbitrary physical drift c is independent of the F2 hard-coded jump-removed Y increment, solving that nontrivial interface without surrogate processes.
-- source:
--   Proved original physical finite J variation mixed bound 7c88cd82; arithmetic epsilon argument; no changed source law.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_drift_mixed_commutator_J_variation_bound

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_discounted_arbitrary_shift_mixed_J_mesh_vanish
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (q : ℝ) (hq : 0 ≤ q) :
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
        (∀ ε : ℝ, 0 < ε →
          ∀ᶠ m in Filter.atTop, ∀ i, i < n m →
            |w (z m i + c m i - j m i) - w (z m i + c m i) -
              w (z m i - j m i) + w (z m i)| ≤ ε * |j m i|) →
        ∀ η : ℝ, 0 < η →
          ∀ᶠ m in Filter.atTop,
            |∑ i ∈ Finset.range (n m),
              Real.exp (-(q * (u m i : ℝ))) *
                (w (z m i + c m i - j m i) - w (z m i + c m i) -
                  w (z m i - j m i) + w (z m i))| < η := by sorry
