-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b28_original_smallband_predictable_ruinclipped_mesh_zero
-- name    : AvramDividend.Classical.avram_b28_original_smallband_predictable_ruinclipped_mesh_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T09:43:02.278977+00:00
-- url     : https://prove2.me/theorems/5778cd0a-be87-4fbc-bcff-116e41a87b6d
-- title:
--   Original stopped physical-grid predictable small-band gain vanishes for a large-only negative-jump Lévy source
-- statement:
--   On an original Lévy sample path with all nonzero jumps of size at most -1 and no Lévy mass on (-1,0], the exact original intrinsic compensated small-band process is zero at every cutoff and every physical time. Thus any finite source-defined predictable physical-grid small-jump gain, retaining the literal if sigma<=a_i then 0 ruin-clipped stop mask, is zero pathwise for arbitrary mesh, bounded or unbounded weights and arbitrary stopping clock. This verifies a concrete necessary specialisation for the B25 Brownian plus size-two negative compound-Poisson two-noise obstruction, without changing the original integrator or clock.
-- source:
--   Prove2Me accepted original small-band source identity 489c24bc-c9c4-4a4b-b5e8-7713ecb89d64 (15 November 2026), B25 exact small channel source mesh statement

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_b27_original_no_small_band_marks_compensator_zero
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_b28_original_smallband_predictable_ruinclipped_mesh_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν (Ioc (-1 : ℝ) 0) = 0)
    (ω : Ω)
    (hLarge : ∀ u : ℝ≥0, 0 < u →
      (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0 ∨
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤ -1))
    (k : ℕ) (σ : Ω → ℝ≥0)
    (S : Finset ℕ) (a b : ℕ → ℝ≥0) (W : ℕ → Ω → ℝ) :
    (∑ i ∈ S, (if σ ω ≤ a i then 0 else W i ω) *
      (avram_p4_h_gaussian_intrinsic_small_band_compensated X k (b i) ω -
       avram_p4_h_gaussian_intrinsic_small_band_compensated X k (a i) ω)) = 0 := by sorry
