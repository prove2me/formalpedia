-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_original_marked_l2_tail_from_levy_envelope_without_sfinite
-- name    : AvramDividend.Classical.avram_wave4_p1_original_marked_l2_tail_from_levy_envelope_without_sfinite
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T22:46:12.067742+00:00
-- url     : https://prove2.me/theorems/f09e6a4a-ea0e-4821-8d17-e439484fa895
-- title:
--   Automatic Lévy finite-band stopped quadratic tail convergence without assuming sigma-finite intensity
-- statement:
--   For a finite original time/sample measure, a ν-integrable Lévy square envelope g with ν-null zero-energy set, and a measurable stopped reserve-dependent marked square-kernel dominated by Cg, prove quadratic compensator energy outside explicit finite-rate mark bands tends to zero. The proof constructs a genuine countable finite-ν cover B_n={1/n≤g}∪{g=0}, derives SigmaFinite and SFinite ν rather than assuming them, and applies the P1 stopped marked product band-tail theorem to exactly the same kernel and original sample space. No PRM law, Campbell or stochastic martingale is assumed; 04-A remains responsible for identifying the actual source-X compensator.
-- source:
--   P1 null-zero canonical finite-rate mark bands (publication job 3f9b7578) and P1 stopped product quadratic tail cf0d248d canonically Proved; pinned Mathlib Measure.FiniteSpanningSetsIn and SigmaFinite⇒SFinite.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_null_zero_energy_canonical_mark_band_exhaustion
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_stopped_marked_l2_product_band_exhaustion

open MeasureTheory Set Filter Topology
open scoped ENNReal

theorem AvramDividend.Classical.avram_wave4_p1_original_marked_l2_tail_from_levy_envelope_without_sfinite
    {A E : Type*} [MeasurableSpace A] [MeasurableSpace E]
    (μ : Measure A) [IsFiniteMeasure μ] (ν : Measure E)
    (g : E → ℝ≥0∞) (hg : Measurable g)
    (henergy : ∫⁻ z, g z ∂ν < ∞)
    (hzero_null : ν {z | g z = 0} = 0)
    (F : A × E → ℝ≥0∞) (hF : Measurable F)
    (C : ℝ≥0∞) (hC : C < ∞)
    (hdom : ∀ p, F p ≤ C * g p.2) :
    let B : ℕ → Set E := fun n =>
      {z | (n : ℝ≥0∞)⁻¹ ≤ g z} ∪ {z | g z = 0}
    Tendsto (fun n : ℕ =>
      ∫⁻ p in Set.univ ×ˢ (B n)ᶜ, F p ∂μ.prod ν)
      Filter.atTop (nhds (0 : ℝ≥0∞)) := by sorry
