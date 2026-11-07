-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_monotone_grid_exit_clock_localisation_sequence
-- name    : AvramDividend.Classical.avram_wave7_18_original_monotone_grid_exit_clock_localisation_sequence
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T16:50:44.286906+00:00
-- url     : https://prove2.me/theorems/051b5fdf-7969-4c83-bdbb-654807bc80d9
-- title:
--   Nested bounded original reserve grid-exit clocks with positive C² pre-exit localisation
-- statement:
--   Take the genuine controlled post-payment reserve x+X.X(clock k)-rightLimit D(clock k), a monotone deterministic nonnegative clock, and for every finite grid horizon m its first two-sided exit K m. Prove each real-time stopped clock clock(K m) is a stopping time in the original 𝓕.rightCont, the sequence is monotone with m by Mathlib's hittingBtwn_mono_right, K m≤m, and every sample before K m lies in the exact positive C² region {y|0<y∧ENNReal.ofReal y<C} and enjoys ContDiffWithinAt. This is a nested bounded-horizon original-source localisation sequence. It does not assert that the sequence tends to infinity, which would be false once the original reserve exits the fixed band; a further shrinking-near-zero and expanding-near-cap argument is required for full exhaustion.

import Mathlib
import Mathlib.Probability.Process.Stopping
import Mathlib.Probability.Process.HittingTime
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_grid_exit_clock_isStoppingTime_rightCont
import Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_grid_preexit_positive_C2_domain

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_18_original_monotone_grid_exit_clock_localisation_sequence
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (lower upper : ℝ) (hlower : 0 < lower)
    (hcap : ∀ y ∈ Set.Icc lower upper, ENNReal.ofReal y < C)
    (clock : ℕ → ℝ≥0) (hclock : Monotone clock)
    (H : Filtration ℕ mΩ)
    (hH : ∀ k, H k = 𝓕.rightCont (clock k))
    (K : ℕ → Ω → ℕ)
    (hK : ∀ m ω, K m ω = hittingBtwn
      (fun k ω => max (x + X.X (clock k) ω - rightLimit D (clock k) ω - upper)
        (lower - (x + X.X (clock k) ω - rightLimit D (clock k) ω)))
      (Set.Ioi (0 : ℝ)) 0 m ω) :
    (∀ m, IsStoppingTime 𝓕.rightCont
      (fun ω : Ω => (clock (K m ω) : WithTop ℝ≥0))) ∧
    (∀ ω : Ω, Monotone (fun m : ℕ => (clock (K m ω) : WithTop ℝ≥0))) ∧
    (∀ m ω, K m ω ≤ m) ∧
    (∀ m ω k, k < K m ω →
      (0 < (x + X.X (clock k) ω - rightLimit D (clock k) ω) ∧
       ENNReal.ofReal (x + X.X (clock k) ω - rightLimit D (clock k) ω) < C) ∧
      ContDiffWithinAt ℝ 2 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}
        (x + X.X (clock k) ω - rightLimit D (clock k) ω)) := by sorry
