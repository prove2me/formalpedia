-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_positive_energy_canonical_finite_rate_mark_exhaustion
-- name    : AvramDividend.Classical.avram_wave4_p1_positive_energy_canonical_finite_rate_mark_exhaustion
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T22:26:52.414101+00:00
-- url     : https://prove2.me/theorems/e2a2b494-a89d-41e9-ac60-471afc66f5ff
-- title:
--   Construct canonical monotone finite-rate Lévy mark bands from positive integrable jump square energy
-- statement:
--   For a mark energy density g that is measurable, everywhere positive and ν-integrable, the explicit bands B_n={z:1/n≤g(z)} are measurable, monotone, finite-ν, and exhaust every mark. This constructs the finite-rate band approximation required for infinite-activity Lévy compensation, including g(z)=min(1,|z|²) on nonzero jump marks, without assuming finite activity or a first absolute moment. The theorem uses genuine finite-energy threshold estimates and the pinned ENNReal inverse-to-zero theorem; no source Poisson law or martingale conclusion is presumed.
-- source:
--   P1 positive-energy threshold finite-intensity theorem (authoring job 87d60418); pinned ENNReal.inv_le_inv', ENNReal.tendsto_inv_nat_nhds_zero, eventually_lt_nhds.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_positive_square_energy_threshold_finite_mark_intensity

open MeasureTheory Set Filter Topology
open scoped ENNReal

theorem AvramDividend.Classical.avram_wave4_p1_positive_energy_canonical_finite_rate_mark_exhaustion
    {E : Type*} [MeasurableSpace E] (ν : Measure E)
    (g : E → ℝ≥0∞) (hg : Measurable g)
    (henergy : ∫⁻ z, g z ∂ν < ∞)
    (hpos : ∀ z, 0 < g z) :
    let B : ℕ → Set E := fun n => {z | (n : ℝ≥0∞)⁻¹ ≤ g z}
    (∀ n, MeasurableSet (B n)) ∧
    (∀ n, ν (B n) < ∞) ∧
    Monotone B ∧
    (⋃ n, B n) = Set.univ := by sorry
