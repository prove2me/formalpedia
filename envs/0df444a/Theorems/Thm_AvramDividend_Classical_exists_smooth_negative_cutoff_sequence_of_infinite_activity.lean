-- Prove2me | Theorems.Thm_AvramDividend_Classical_exists_smooth_negative_cutoff_sequence_of_infinite_activity
-- name    : AvramDividend.Classical.exists_smooth_negative_cutoff_sequence_of_infinite_activity
-- status  : Open
-- author  : @WillR
-- created : 2026-10-28T11:57:06.357842+00:00
-- url     : https://prove2.me/theorems/57ebfabc-8c17-4ac1-9953-a085a3e57ffd
-- title:
--   Smooth negative cutoff sequence detects infinite Levy activity
-- statement:
--   If a spectrally negative Levy measure has infinite mass on the negative halfline, there is a sequence of nonnegative smooth compactly supported tests, bounded by one, supported strictly below zero and vanishing near zero, whose integrals against the negative Levy measure diverge.
-- source:
--   Source-faithful child for AvramDividend.Classical.barrier_zero_boundary_value (9e8e88ea-7f12-4d95-a4d1-a54abfee9305), pinned at Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474. The real-cutoff Fourier/mesh source already constructs the dyadic negative bump sequence and proves smoothness, compact support, range [0,1], vanishing near zero, integrability, and divergence of its restricted Levy integrals (candidates/work_on/AvramDividend_Classical_barrier_zero_boundary_value_9e8e88ea_fourier_partition_20261028.lean, lines 3451-4080). This isolates a genuine analytic step used to turn infinite negative activity into mesh hit-rate lower bounds. The child depends only on X and its Levy measure; it does not depend on the parent theorem, so it creates no cycle. The publication declares a new Open problem only: no parent-child edge or proof of barrier_zero_boundary_value is claimed, and the formal bridge remains to be established through the early-jump mesh argument.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open AvramDividend.Classical
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.exists_smooth_negative_cutoff_sequence_of_infinite_activity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hνinf : X.ν (Iio (0 : ℝ)) = ⊤) :
    ∃ f : ℕ → ℝ → ℝ,
      (∀ n,
        ContDiff ℝ ⊤ (f n) ∧
        HasCompactSupport (f n) ∧
        Function.support (f n) ⊆ Iio (0 : ℝ) ∧
        (∀ x : ℝ, 0 ≤ f n x ∧ f n x ≤ 1) ∧
        (∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ, |x| < δ → f n x = 0) ∧
        Integrable (f n) (X.ν.restrict (Iio (0 : ℝ)))) ∧
      Filter.Tendsto
        (fun n : ℕ => ∫ y, f n y ∂(X.ν.restrict (Iio (0 : ℝ))))
        atTop atTop := by sorry
