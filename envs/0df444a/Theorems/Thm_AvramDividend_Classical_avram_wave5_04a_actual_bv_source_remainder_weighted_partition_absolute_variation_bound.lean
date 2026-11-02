-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_remainder_weighted_partition_absolute_variation_bound
-- name    : AvramDividend.Classical.avram_wave5_04a_actual_bv_source_remainder_weighted_partition_absolute_variation_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T11:49:00.870999+00:00
-- url     : https://prove2.me/theorems/2496fb55-e8d1-455f-9cea-0728d868c5b9
-- title:
--   Actual original BV source residual: sharp absolute bound for weighted finite-partition variation
-- statement:
--   For the actual spectrally negative Levy source with bounded variation, almost surely there is one explicitly defined nondecreasing source residual after subtracting all intrinsic negative left jumps. Every ordered deterministic or random samplewise partition and every real weight sequence bounded in modulus by M has weighted residual sum bounded in absolute value by M times the exact endpoint residual increment. The result supplies a finite-variation uniform bound for controlling C1 approximation errors without an Ito-Meyer theorem.
-- source:
--   Chat04-A original-process finite-variation helper, derived from canonically Proved monotonicity 019edf01-4961-4bf1-805e-b935366106bb, absolute value triangle inequality, and telescoping weighted variations.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_canonical_remainder_monotone

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- A pathwise uniform bound on arbitrary weighted source-remainder sums,
deduced from the monotonicity of the residual of the original BV source. -/

theorem AvramDividend.Classical.avram_wave5_04a_actual_bv_source_remainder_weighted_partition_absolute_variation_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∃ R : ℝ≥0 → ℝ,
      (∀ t : ℝ≥0,
        R t = ((t : ℝ) * X.drift - X.X t ω) -
          (∑' (v : ℝ≥0),
            if 0 < v ∧ v ≤ t then
              ENNReal.ofReal (Function.leftLim
                (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
            else 0).toReal) ∧
      Monotone R ∧
      ∀ (u : ℕ → ℝ≥0) (hu : Monotone u) (n : ℕ)
        (a : ℕ → ℝ) (M : ℝ) (hM : 0 ≤ M)
        (ha : ∀ i : ℕ, |a i| ≤ M),
        |(Finset.range n).sum (fun i =>
          a i * (R (u (i + 1)) - R (u i)))| ≤
          M * (R (u n) - R (u 0)) := by sorry
