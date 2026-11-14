-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB235_nested_expected_time_discounted_clipping_error_bound
-- name    : AvramDividend.Classical.avram_gbB235_nested_expected_time_discounted_clipping_error_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T08:26:19.608359+00:00
-- url     : https://prove2.me/theorems/3e5de7fd-93aa-4ab2-9062-aedfb90ea75e
-- title:
--   Integrated expected squared discrepancy of discounted nested clips is bounded by two-strip occupation integral
-- statement:
--   Given two measures, an arbitrary sample-dependent spatial process, a nonnegative physical-time parameter and nonnegative discount rate, the double iterated integral of squared discrepancy between two nested discounted gradient clips is bounded by four times the squared clip amplitude multiplied by the corresponding double integral of the two boundary-strip indicators, provided both sides are integrable. This is the quantitative link between selected-good-cutoff L2 and prescribed-cutoff occupation estimates.
-- source:
--   Gaussian B65 fixed-boundary bridge, integrates Proved B226 by inner and outer integral_mono; distinct from the genuinely hard fixed-level occupation B100.

import Mathlib
import Mathlib.Analysis.Calculus.Deriv.Basic
open MeasureTheory Set Filter Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB235_nested_expected_time_discounted_clipping_error_bound
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β)
    (w : ℝ → ℝ) (a a' b' b B q : ℝ)
    (ha : a ≤ a') (hab : a' ≤ b') (hb : b' ≤ b)
    (hB : 1 ≤ B)
    (hgrad : ∀ y ∈ Set.Icc a b, |deriv w y| ≤ B)
    (hq : 0 ≤ q)
    (Y : α → β → ℝ) (t : α → ℝ) (ht : ∀ s, 0 ≤ t s) :
    let G : α → β → ℝ := fun s ω =>
      (Real.exp (-(q * t s)) *
          (if Y s ω ∈ Set.Icc a b then deriv w (Y s ω) else 1) -
        Real.exp (-(q * t s)) *
          (if Y s ω ∈ Set.Icc a' b' then deriv w (Y s ω) else 1))^2
    let J : α → β → ℝ := fun s ω =>
      4 * B^2 *
        (if Y s ω ∈ Set.Icc a a' ∨ Y s ω ∈ Set.Icc b' b
          then (1 : ℝ) else 0)
    (∀ s, Integrable (G s) ν) →
    (∀ s, Integrable (J s) ν) →
    Integrable (fun s => ∫ ω, G s ω ∂ν) μ →
    Integrable (fun s => ∫ ω, J s ω ∂ν) μ →
    (∫ s, (∫ ω, G s ω ∂ν) ∂μ) ≤
      (∫ s, (∫ ω, J s ω ∂ν) ∂μ) := by sorry
