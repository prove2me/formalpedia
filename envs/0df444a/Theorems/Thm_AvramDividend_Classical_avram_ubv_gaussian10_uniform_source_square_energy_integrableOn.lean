-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian10_uniform_source_square_energy_integrableOn
-- name    : AvramDividend.Classical.avram_ubv_gaussian10_uniform_source_square_energy_integrableOn
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T12:16:01.129006+00:00
-- url     : https://prove2.me/theorems/889e6829-b0af-481a-8cda-79b9c1936264
-- title:
--   Bounded original time sections have pathwise finite square energy
-- statement:
--   An arbitrary real-valued integrand on the original time-sample product with measurable time sections and a deterministic uniform absolute bound has square-integrable time sections on every finite-measure horizon, for every sample point. No completion, null-set modification or replacement process is used; the lemma discharges the Gaussian stopped-bracket pathwise-energy assumption once the actual coefficient is known to have measurable time sections and a uniform bound.
-- source:
--   Pinned Mathlib IntegrableOn.of_bound and Measurable.pow_const; explicit finite-window time measure.

import Mathlib

open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_gaussian10_uniform_source_square_energy_integrableOn
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (H : ℝ≥0 × Ω → ℝ)
    (hH : ∀ ω, Measurable (fun t : ℝ≥0 => H (t, ω)))
    (μtime : Measure ℝ≥0) (T : ℝ≥0)
    (hFinite : μtime (Ioc (0 : ℝ≥0) T) < ⊤)
    (C : ℝ) (hC : 0 ≤ C)
    (hBound : ∀ p, |H p| ≤ C) :
    ∀ ω, IntegrableOn (fun t : ℝ≥0 => (H (t, ω)) ^ 2)
      (Ioc (0 : ℝ≥0) T) μtime := by sorry
