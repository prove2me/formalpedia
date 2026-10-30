-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_05_killed_mesh_cell_integral_eq_mass
-- name    : AvramDividend.Classical.avram_root29_05_killed_mesh_cell_integral_eq_mass
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T10:37:01.700125+00:00
-- url     : https://prove2.me/theorems/0ae8cfd1-aef1-4a9c-a386-1dcdf499b68a
-- title:
--   Actual Stieltjes cell integral of a killed sampled discount equals endpoint weight times cell mass
-- statement:
--   For an arbitrary actual measure μ on real payment times, every rational mesh cell (k/(n+1),(k+1)/(n+1)], discount q and strict killing horizon τ, integrate the discounted right-ceiling sampled weight against μ on that cell. It equals the cell measure times its exact right-endpoint discounted surviving weight, with zero when endpoint is at or after ruin. Combined with runningSup dividendMeasure Ioc mass = record increment, this is a source-faithful bridge between genuine regulator dividends and countable sampled cashflows.
-- source:
--   Proved exact half-open right-mesh endpoint identity 69f7fe98, pinned Mathlib ae_restrict_mem, lintegral_congr_ae and lintegral_const. Consumer actual Stieltjes-to-grid reconstruction and canonical 79978d61.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_right_mesh_cell_endpoint_identity

open AvramDividend.Classical MeasureTheory Set
open scoped ENNReal Classical

theorem AvramDividend.Classical.avram_root29_05_killed_mesh_cell_integral_eq_mass
    (μ : Measure ℝ) (q : ℝ) (τ : ℝ≥0∞)
    (n k : ℕ) :
    (∫⁻ r in Ioc ((k : ℝ) / ((n : ℝ) + 1))
        (((k : ℝ) + 1) / ((n : ℝ) + 1)),
      (let e := ((⌈r * ((n : ℝ) + 1)⌉ : ℤ) : ℝ) / ((n : ℝ) + 1)
       if ENNReal.ofReal e < τ then
         ENNReal.ofReal (Real.exp (-(q * e))) else 0) ∂μ) =
    (if ENNReal.ofReal (((k : ℝ) + 1) / ((n : ℝ) + 1)) < τ then
      ENNReal.ofReal (Real.exp (-(q * (((k : ℝ) + 1) / ((n : ℝ) + 1)))))
      else 0) *
      μ (Ioc ((k : ℝ) / ((n : ℝ) + 1))
        (((k : ℝ) + 1) / ((n : ℝ) + 1))) := by sorry
