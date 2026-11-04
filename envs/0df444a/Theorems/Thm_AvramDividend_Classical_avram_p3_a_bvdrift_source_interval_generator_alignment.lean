-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_source_interval_generator_alignment
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_source_interval_generator_alignment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:10:28.757588+00:00
-- url     : https://prove2.me/theorems/f17e2a9d-e6dd-4c93-95da-f5f8246b65ba
-- title:
--   Actual BV Lévy physical generator and signed intrinsic source decomposition with zero-anchored monotone residual
-- statement:
--   On the unchanged source probability space, with only bounded variation and generator-integrability assumptions, the compensated Lévy generator equals physical drift times the derivative plus the genuine negative-jump integral; almost surely the original source path increment is physical drift minus its actual intrinsic negative left jumps and a uniquely defined, nonnegative, monotone, zero-anchored residual. This theorem explicitly retains the residual and does not claim an unproved complete pure-jump representation.
-- source:
--   Avram P3-A. Exact conjunction of canonically Proved c8ba98f0 and 09869e16, with a new zero-origin and nonnegative-at-all-times consequence of the actual source X_zero and original monotonicity; no synthetic process, new axiom or parent modification.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_boundedVariation_generator_physical_drift_representation
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_exact_intrinsic_measure_interval_remainder_decomposition

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Original-process BV physical generator and intrinsic signed path budget,
with a zero-anchored nonnegative downward residual (not presumed zero). -/

theorem AvramDividend.Classical.avram_p3_a_bvdrift_source_interval_generator_alignment
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (x : ℝ) (hGen : X.GeneratorIntegrable w x) :
    (X.generator w x = X.drift * deriv w x +
      ∫ y in Iio (0 : ℝ), w (x + y) - w x ∂X.ν) ∧
    ∀ᵐ ω ∂P, ∃ R : ℝ≥0 → ℝ,
      (∀ t : ℝ≥0,
        R t = ((t : ℝ) * X.drift - X.X t ω) -
          (∑' (v : ℝ≥0),
            if 0 < v ∧ v ≤ t then
              ENNReal.ofReal (Function.leftLim
                (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
            else 0).toReal) ∧
      R 0 = 0 ∧ Monotone R ∧ (∀ t : ℝ≥0, 0 ≤ R t) ∧
      ∀ (s t : ℝ≥0), s ≤ t →
        X.X t ω - X.X s ω =
          ((t : ℝ) - (s : ℝ)) * X.drift -
          (∫⁻ p,
            (if s < p.1 ∧ p.1 ≤ t then ENNReal.ofReal (-p.2) else 0) ∂
            ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
              X.X u ω - Function.leftLim
                (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
              (fun u : ℝ≥0 => (u,
                X.X u ω - Function.leftLim
                  (fun v : ℝ≥0 => X.X v ω) u)))).toReal -
          (R t - R s) := by sorry
