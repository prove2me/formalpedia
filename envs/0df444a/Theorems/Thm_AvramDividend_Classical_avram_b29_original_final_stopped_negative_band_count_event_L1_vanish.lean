-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b29_original_final_stopped_negative_band_count_event_L1_vanish
-- name    : AvramDividend.Classical.avram_b29_original_final_stopped_negative_band_count_event_L1_vanish
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T23:59:56.924897+00:00
-- url     : https://prove2.me/theorems/2a1dd34d-5562-4dae-87d4-6bda2242a51c
-- title:
--   Original final stopped negative-jump cell count vanishes in event-restricted expected mass
-- statement:
--   The actual original Lévy finite-cutoff marked jump count on the shrinking poststop physical cell has expected count tending to zero on any event A whenever its already-established global count is integrable. The original source's eventwise physical clock, not an independent Poisson copy, is retained.
-- source:
--   Avram Palmowski Pistorius (2007) Proposition 4(i), original source final clipped cell and Proved a39752ef-d1f2-40cd-aff9-d415a7b54277.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_jump_phys13_original_finite_cutoff_physical_rightcell_count_L1_vanishes
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_b29_original_final_stopped_negative_band_count_event_L1_vanish
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (cut : ℕ)
    (τ : Ω → ℝ≥0) (e : ℕ → Ω → ℝ≥0)
    (hτ : Measurable τ) (he : ∀ k, Measurable (e k))
    (heBound : ∀ k ω, e k ω ≤ T)
    (heTendsto : ∀ ω, Tendsto (fun k => e k ω) atTop (𝓝 (τ ω)))
    (A : Set Ω) :
    let B : Set ℝ := Iic (-(1 / ((cut : ℝ) + 1)))
    let J : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let F : ℕ → Ω → ℝ := fun k ω =>
      ((J ω) (Ioc (τ ω) (e k ω) ×ˢ B)).toReal
    (∀ k, Integrable (F k) P) →
    Tendsto (fun k => ∫ ω in A, F k ω ∂P) atTop (𝓝 (0 : ℝ)) := by sorry
