-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_redux15_original_jump_cutoff_exponential_ae_tendsto
-- name    : AvramDividend.Classical.avram_redux15_original_jump_cutoff_exponential_ae_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T11:15:04.704606+00:00
-- url     : https://prove2.me/theorems/88a590a4-3e73-4c5d-a6f2-c971abc9ffb6
-- title:
--   Original bounded variation genuine jump cutoff exponentials converge almost surely
-- statement:
--   For each integer horizon, the exponential of the actual original spectrally negative Lévy downward-jump magnitude sum, restricted to jumps strictly larger than reciprocal cutoff, converges almost surely to the exponential of the complete actual-jump sum. Bounded variation gives a finite total magnitude almost surely, and the cutoffs decrease to zero.
-- source:
--   Authentic original BV path; canonical physical jumps, almost sure finite total from avram_p3_a_bvdrift_original_interval_negative_jump_tsum_lt_top.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_redux15_original_jump_cutoff_exponential_ae_tendsto
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ n : ℕ, ∀ᵐ ω ∂P,
      Tendsto (fun k : ℕ => Real.exp (-((∑' v : ℝ≥0,
        if 0 < v ∧ v ≤ (n : ℝ≥0) ∧
          (1 / ((k : ℝ) + 1)) < (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω) then
          ENNReal.ofReal
            (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
        else 0).toReal))) atTop
        (𝓝 (Real.exp (-((∑' v : ℝ≥0,
        if 0 < v ∧ v ≤ (n : ℝ≥0) then
          ENNReal.ofReal
            (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
        else 0).toReal)))) := by sorry
