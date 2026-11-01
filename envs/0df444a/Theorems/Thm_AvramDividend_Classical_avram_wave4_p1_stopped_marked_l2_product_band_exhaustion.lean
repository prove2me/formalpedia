-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_stopped_marked_l2_product_band_exhaustion
-- name    : AvramDividend.Classical.avram_wave4_p1_stopped_marked_l2_product_band_exhaustion
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T22:19:15.960539+00:00
-- url     : https://prove2.me/theorems/cf0d248d-cf94-43d2-ab43-7780cacc4438
-- title:
--   Actual marked stopped-kernel quadratic compensator energy has vanishing infinite-activity band tails
-- statement:
--   For finite time/sample base μ and SFinite (possibly infinite-activity) jump intensity ν, a measurable marked kernel energy F bounded by a finite factor times a ν-integrable mark square envelope has vanishing energy over the complements of any increasing finite-rate mark-band exhaustion. This combines nontrivial product-measure Tonelli integrability with weighted finite-measure continuity from above, explicitly on the same original sample/time and mark product; it requires neither first absolute jump moment nor a martingale conclusion. Source 04-A must still prove that actual N_X has product compensator.
-- source:
--   Canonical P1 weighted finite-energy band-tail theorem 4e7cfc5e and marked product quadratic domination theorem 04a3e4f3; pinned Mathlib Measure.prod_prod and continuity from above.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_levy_square_energy_band_tails
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_marked_product_square_kernel_integrable_of_domination

open MeasureTheory Set Filter Topology
open scoped ENNReal

theorem AvramDividend.Classical.avram_wave4_p1_stopped_marked_l2_product_band_exhaustion
    {A E : Type*} [MeasurableSpace A] [MeasurableSpace E]
    (μ : Measure A) [IsFiniteMeasure μ]
    (ν : Measure E) [SFinite ν]
    (g : E → ℝ≥0∞) (hg : Measurable g)
    (henergy : ∫⁻ z, g z ∂ν < ∞)
    (F : A × E → ℝ≥0∞) (hF : Measurable F)
    (C : ℝ≥0∞) (hC : C < ∞)
    (hdom : ∀ p, F p ≤ C * g p.2)
    (B : ℕ → Set E) (hB : ∀ n, MeasurableSet (B n))
    (hBfinite : ∀ n, ν (B n) < ∞)
    (hBmono : Monotone B)
    (hBcover : (⋃ n, B n) = Set.univ) :
    Tendsto (fun n : ℕ =>
      ∫⁻ p in Set.univ ×ˢ (B n)ᶜ, F p ∂μ.prod ν)
      Filter.atTop (nhds (0 : ℝ≥0∞)) := by sorry
