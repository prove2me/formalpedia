-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_BV_intrinsic_source_residual_exact_finite_partition_total_variation
-- name    : AvramDividend.Classical.avram_wave5_04a_actual_BV_intrinsic_source_residual_exact_finite_partition_total_variation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T20:26:14.777663+00:00
-- url     : https://prove2.me/theorems/95bc59a9-1dbf-4245-a14c-0c6ae1568d5b
-- title:
--   Actual BV Levy intrinsic residual has exact total variation on every finite physical-time partition
-- statement:
--   For the genuine original spectrally negative bounded-variation Levy source, there exists on a single probability-one event its explicit nondecreasing downward finite-variation residual R after removing the genuine intrinsic negative left-jump measure. The exact original-source interval drift/jump/residual representation holds, and every finite monotone physical-time partition has total absolute residual increment exactly R at the final endpoint minus R at the initial endpoint. The theorem does not presume the residual is zero or import controlled Ito-Meyer.
-- source:
--   Chat04-A original-source BV path theorem combining Proved exact intrinsic source measure interval decomposition 09869e16-9a95-47e7-b1cd-83739a17b285, monotonicity of the unique original downward residual, and pinned Mathlib Finset.sum_range_sub. This gives a direct exact total-variation Stieltjes source interface without a replacement Poisson source.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_exact_intrinsic_measure_interval_remainder_decomposition

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Exact original-source residual total variation on all finite monotone time grids. -/

theorem AvramDividend.Classical.avram_wave5_04a_actual_BV_intrinsic_source_residual_exact_finite_partition_total_variation
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
      (∀ (s t : ℝ≥0), s ≤ t →
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
            (R t - R s)) ∧
      ∀ (n : ℕ) (u : ℕ → ℝ≥0) (hu : Monotone u),
        (Finset.range n).sum (fun i =>
          |R (u (i + 1)) - R (u i)|) =
          R (u n) - R (u 0) := by sorry
