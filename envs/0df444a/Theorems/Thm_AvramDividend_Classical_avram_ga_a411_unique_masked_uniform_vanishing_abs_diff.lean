-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a411_unique_masked_uniform_vanishing_abs_diff
-- name    : AvramDividend.Classical.avram_ga_a411_unique_masked_uniform_vanishing_abs_diff
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T18:20:40.166739+00:00
-- url     : https://prove2.me/theorems/15c61784-947f-468b-9fcb-6cfe252b85e1
-- title:
--   One-active finite masked absolute increments tend to zero under uniform raw and drift control
-- statement:
--   An at-most-one-active-cell masked absolute sum tends to zero if every cell raw increment becomes uniformly small and a shared scalar drift correction tends to zero.
-- source:
--   Proved a394 one-active absolute mask sum domination; elementary triangle inequality and epsilon control.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Filter Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a411_unique_masked_uniform_vanishing_abs_diff
    (Mask : ℕ → ℕ → Prop) [∀ m i, Decidable (Mask m i)]
    (F : ℕ → ℕ → ℝ) (d : ℕ → ℝ)
    (hUnique : ∀ m i j, Mask m i → Mask m j → i = j)
    (hRaw : ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop,
      ∀ i < m, |F m i| < ε / 2)
    (hDrift : ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop,
      |d m| ≤ ε / 2) :
    Tendsto (fun m : ℕ =>
      ∑ i ∈ Finset.range m, if Mask m i then |F m i - d m| else 0)
      atTop (𝓝 (0 : ℝ)) := by sorry
