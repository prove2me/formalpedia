-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_dyadic_uniform_active_expected_le_intensity
-- name    : AvramDividend.Classical.bv_dyadic_uniform_active_expected_le_intensity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T13:09:49.713617+00:00
-- url     : https://prove2.me/theorems/1d283aff-5e0c-4d16-a34c-8f7927fc1c2f
-- title:
--   Uniform intensity upper bound on expected number of active equal-length Lévy cells
-- statement:
--   For N>0 measurable equal-length cell events whose real probabilities are all 1−exp(−λT/N), their expected count (as an extended nonnegative Lebesgue integral of the indicator sum) is bounded by λT. This uses finite linearity of the nonnegative integral, finite probability to convert real-valued event probabilities back to ENNReal, and the universal exponential inequality 1−exp(−u)≤u. Crucially, independence between the events is not needed. It is the core uniform moment estimate for the actual bounded-variation Lévy residual dyadic positive-increment count.
-- source:
--   Avram, Palmowski, Pistorius (2007), finite-activity spectrally negative Lévy first-jump law, dyadic argument.

import Theorems.Thm_AvramDividend_Classical_bv_dyadic_lintegral_active_cell_count
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic

open AvramDividend.Classical MeasureTheory Finset
open scoped ENNReal

theorem AvramDividend.Classical.bv_dyadic_uniform_active_expected_le_intensity
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (E : ℕ → Set Ω) (N : ℕ) (hN : 0 < N)
    (rate horizon : ℝ)
    (hE : ∀ i : ℕ, i < N → MeasurableSet (E i))
    (hp : ∀ i : ℕ, i < N →
      P.real (E i) =
        1 - Real.exp (-(rate * horizon / (N : ℝ)))) :
    (∫⁻ ω, ∑ i ∈ Finset.range N,
      (E i).indicator (fun _ => (1 : ℝ≥0∞)) ω ∂P) ≤
      ENNReal.ofReal (rate * horizon) := by sorry
