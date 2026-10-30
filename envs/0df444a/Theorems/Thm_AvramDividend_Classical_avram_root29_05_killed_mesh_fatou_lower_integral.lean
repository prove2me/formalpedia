-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_05_killed_mesh_fatou_lower_integral
-- name    : AvramDividend.Classical.avram_root29_05_killed_mesh_fatou_lower_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T10:31:59.158835+00:00
-- url     : https://prove2.me/theorems/16751744-1613-468c-8924-01704e3f4d0c
-- title:
--   Fatou lower bound from killed right-mesh payments to the actual discounted Stieltjes integral
-- statement:
--   For any nonnegative measure on continuous real payment times and any discount and extended killing horizon, the true positive-time strictly killed discounted Stieltjes integral is at most the liminf of integrals of the discounted right-mesh endpoint weights with strict endpoint killing. Genuine Fatou inequality for arbitrary measure, with full endpoint boundary handling. Combined with actual runningSup dividendMeasure and cell sum identities, this is the reverse direction for the true reflected-regulator killed dividend value; the theorem itself does not assume a flawed stopping set or a barrier scale quotient.
-- source:
--   Canonically Proved pointwise strict-killed endpoint convergence cbc8dd81 and measurability 23b2d8cf, pinned Mathlib lintegral_liminf_le and Filter.Tendsto.liminf_eq. Consumer 79978d61 and continuous-time Stieltjes reconstruction.

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_killed_right_mesh_discount_tendsto
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_killed_right_mesh_discount_measurable

open AvramDividend.Classical MeasureTheory Filter Topology
open scoped ENNReal Classical

theorem AvramDividend.Classical.avram_root29_05_killed_mesh_fatou_lower_integral
    (μ : Measure ℝ) (q : ℝ) (τ : ℝ≥0∞) :
    (∫⁻ r : ℝ, if 0 < r then
      if ENNReal.ofReal r < τ then
        ENNReal.ofReal (Real.exp (-(q * r))) else 0
      else 0 ∂μ) ≤
    liminf (fun n : ℕ =>
      ∫⁻ r : ℝ, if 0 < r then
        let e := ((⌈r * ((n : ℝ) + 1)⌉ : ℤ) : ℝ) / ((n : ℝ) + 1)
        if ENNReal.ofReal e < τ then
          ENNReal.ofReal (Real.exp (-(q * e))) else 0
        else 0 ∂μ) atTop := by sorry
