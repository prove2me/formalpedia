-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_signed_l1_stopped_marked_band_tail
-- name    : AvramDividend.Classical.avram_wave4_p1_signed_l1_stopped_marked_band_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T00:02:25.156657+00:00
-- url     : https://prove2.me/theorems/473532ea-ef37-42fd-932e-fadfa3b1dcff
-- title:
--   Any integrable signed stopped marked kernel has vanishing L¹ finite-band compensator tails
-- statement:
--   For finite original time/sample measure μ, a σ-finite or SFinite mark intensity ν, and any measurable signed kernel F integrable for μ⊗ν, prove the absolute L¹ mass of F over the complementary marks to finite-ν increasing measurable exhausting bands B_n tends to zero. This uses actual integrability rather than a square-envelope domination; it is suitable for BV stopped dividend-source jump kernels and does not assume a Poisson compensator law or full predictable Campbell identity. The proof reduces to the already Proved weighted-measure complement-tail theorem on the same product space.
-- source:
--   P1 canonical levysquare_energy_band_tails 4e7cfc5e Proved; pinned Mathlib Integrable.hasFiniteIntegral, Measure.prod_prod and measurable_enorm.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_levy_square_energy_band_tails

open MeasureTheory Set Filter Topology
open scoped ENNReal

theorem AvramDividend.Classical.avram_wave4_p1_signed_l1_stopped_marked_band_tail
    {A E : Type*} [MeasurableSpace A] [MeasurableSpace E]
    (μ : Measure A) [IsFiniteMeasure μ]
    (ν : Measure E) [SFinite ν]
    (F : A × E → ℝ) (hFm : Measurable F)
    (hFi : Integrable F (μ.prod ν))
    (B : ℕ → Set E) (hB : ∀ n, MeasurableSet (B n))
    (hBfinite : ∀ n, ν (B n) < ∞)
    (hBmono : Monotone B)
    (hBcover : (⋃ n, B n) = Set.univ) :
    Tendsto (fun n : ℕ =>
      ∫⁻ p in Set.univ ×ˢ (B n)ᶜ, ‖F p‖ₑ ∂μ.prod ν)
      Filter.atTop (nhds (0 : ℝ≥0∞)) := by sorry
