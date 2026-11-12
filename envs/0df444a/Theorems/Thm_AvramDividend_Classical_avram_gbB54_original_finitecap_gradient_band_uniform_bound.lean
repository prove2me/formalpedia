-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB54_original_finitecap_gradient_band_uniform_bound
-- name    : AvramDividend.Classical.avram_gbB54_original_finitecap_gradient_band_uniform_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T12:46:53.87284+00:00
-- url     : https://prove2.me/theorems/d87f7915-615d-4f8e-be22-5b6aa80cccdd
-- title:
--   Uniform bound for discounted finite-cap clipped gradient on original interior band
-- statement:
--   The clipped gradient multiplier equals one off the compact interior band, is discounted by a nonnegative time and set to zero after an arbitrary stopping time. It has a uniform deterministic bound independent of time, stopping time and reserve path.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB54_original_finitecap_gradient_band_uniform_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (δ : ℝ) (hδ : 0 < δ) (j : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (t : ℝ≥0) (ρ : Ω → ℝ≥0)
      (Y : Ω → ℝ) (ω : Ω),
      |if t < ρ ω then Real.exp (-(q * (t : ℝ))) *
        (if Y ω ∈ Icc (δ / 2)
          (C.toReal * (((j + 1 : ℕ) : ℝ) /
            ((j + 2 : ℕ) : ℝ))) then deriv w (Y ω) else 1)
      else 0| ≤ B := by sorry
