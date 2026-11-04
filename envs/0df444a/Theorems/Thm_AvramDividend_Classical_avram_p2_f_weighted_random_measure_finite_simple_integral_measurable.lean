-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_random_measure_finite_simple_integral_measurable
-- name    : AvramDividend.Classical.avram_p2_f_weighted_random_measure_finite_simple_integral_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T13:44:43.493108+00:00
-- url     : https://prove2.me/theorems/a5012d56-046e-4e54-8f67-2ce0881a2973
-- title:
--   Finite predictable-simple random measure integral is measurable from genuine marked-cell mass kernels
-- statement:
--   For an arbitrary sample-dependent measure M_ω, a finite family of marked measurable sets C_i and nonnegative random coefficients H_i(ω), the outer random variable ω↦∫ Σ_i H_i(ω)1_Ci(x) M_ω(dx) is measurable provided each original cell mass ω↦M_ω(C_i) and each coefficient H_i are separately measurable. The proof converts the inner integral pathwise to the finite sum of actual cell masses and applies finite-sum measurability. It supplies the explicit outer-measurability bridge required to use the separate double-monotone convergence lemma for original Lévy predictable simple integrands; no generic random-kernel measurability, Poisson substitution or Lévy ν rate is assumed.
-- source:
--   Pinned Mathlib lintegral_finset_sum, lintegral_indicator and Finset.measurable_sum, actual-measure cell-mass hMass explicit.

import Mathlib

open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.avram_p2_f_weighted_random_measure_finite_simple_integral_measurable
    {Ω α ι : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (M : Ω → Measure α) (S : Finset ι)
    (C : ι → Set α) (hC : ∀ i ∈ S, MeasurableSet (C i))
    (H : ι → Ω → ℝ≥0∞)
    (hH : ∀ i ∈ S, Measurable (H i))
    (hMass : ∀ i ∈ S, Measurable (fun ω => M ω (C i))) :
    Measurable (fun ω =>
      (∫⁻ x, S.sum (fun i => (C i).indicator (fun _ => H i ω) x) ∂M ω)) := by sorry
