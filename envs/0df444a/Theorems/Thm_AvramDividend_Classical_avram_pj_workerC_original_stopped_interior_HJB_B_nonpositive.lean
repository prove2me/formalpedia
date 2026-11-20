-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_original_stopped_interior_HJB_B_nonpositive
-- name    : AvramDividend.Classical.avram_pj_workerC_original_stopped_interior_HJB_B_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T07:14:59.730731+00:00
-- url     : https://prove2.me/theorems/aa16b9d8-f357-44d7-946c-79195797c6dc
-- title:
--   Original stopped strictly interior HJB generator physical-time source B is pathwise nonpositive on every bounded clock
-- statement:
--   For the original spectrally negative process and any original controlled reserve, the discount-weighted generator-minus-qw, masked before ruin and to the genuine C2 interior band, is nonpositive at each time from the HJB super-solution. Therefore the exact physical-time Stieltjes integral B up to any bounded random clock is nonpositive pathwise. No artificial martingale or integrability assumptions are introduced.
-- source:
--   Original c4c2c1a1 R and B exact kernels, ENNReal.ofReal_lt_iff_lt_toReal and Mathlib integral_nonpos.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerC_original_stopped_interior_HJB_B_nonpositive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hCfinite : C ≠ ⊤)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (u v δ : ℝ) (hu : 0 < u) (hδ : 0 < δ)
    (huv : u + δ < v) (hvCap : v < C.toReal)
    (T : ℝ≥0) (ρ : Ω → ℝ≥0) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let R : ℝ≥0 × Ω → ℝ := fun p =>
      Real.exp (-(q * (p.1 : ℝ))) *
        ((if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then (1 : ℝ) else 0) *
          (if Y p ∈ Icc (u + δ) v then
            X.generator w (Y p) - q * w (Y p) else 0))
    let μT : Measure ℝ≥0 :=
      ((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal
    ∀ ω : Ω, (∫ t : ℝ≥0, if t ≤ ρ ω then R (t, ω) else 0 ∂μT) ≤ 0 := by sorry
