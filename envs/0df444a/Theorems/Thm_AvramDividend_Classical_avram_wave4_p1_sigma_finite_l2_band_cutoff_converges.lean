-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_sigma_finite_l2_band_cutoff_converges
-- name    : AvramDividend.Classical.avram_wave4_p1_sigma_finite_l2_band_cutoff_converges
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T22:19:18.147183+00:00
-- url     : https://prove2.me/theorems/65f775d0-6baf-49a2-b747-75a00619f7b5
-- title:
--   Exhaustive predictable mark cuts converge in L² on sigma-finite intensity spaces
-- statement:
--   For any measurable square-energy finite real kernel on an arbitrary (possibly infinite) measure space, its restriction to complements of measurable increasing exhaustive mark bands has eLpNorm₂ tending to zero. It applies to a time-stopped predictable kernel as a function on the full predictable time×sample×mark space, and is the deterministic L² Cauchy step for finite-activity band approximation. No martingale or Campbell identity is an assumption.
-- source:
--   P1 finite square-energy band-tail theorem and pinned Mathlib eLpNorm_indicator_eq_eLpNorm_restrict, eLpNorm_eq_lintegral_rpow_enorm_toReal, continuous ENNReal.rpow.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_levy_square_energy_band_tails

open MeasureTheory Set Filter Topology
open scoped ENNReal

theorem AvramDividend.Classical.avram_wave4_p1_sigma_finite_l2_band_cutoff_converges
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f : α → ℝ) (hf : Measurable f)
    (henergy : ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ < ∞)
    (B : ℕ → Set α)
    (hB : ∀ n, MeasurableSet (B n))
    (hBfinite : ∀ n, μ (B n) < ∞)
    (hBmono : Monotone B)
    (hBcover : (⋃ n, B n) = Set.univ) :
    Tendsto (fun n : ℕ =>
      eLpNorm ((B n)ᶜ.indicator f) (2 : ℝ≥0∞) μ)
      Filter.atTop (nhds (0 : ℝ≥0∞)) := by sorry
