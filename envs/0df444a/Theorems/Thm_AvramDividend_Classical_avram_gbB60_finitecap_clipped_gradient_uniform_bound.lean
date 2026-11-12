-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB60_finitecap_clipped_gradient_uniform_bound
-- name    : AvramDividend.Classical.avram_gbB60_finitecap_clipped_gradient_uniform_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T12:51:26.066597+00:00
-- url     : https://prove2.me/theorems/2a55aeec-3265-48f6-a03c-51924b666dc3
-- title:
--   Clipped interior-band first derivative has a uniform discounted stopped bound
-- statement:
--   Finite C2 regularity on the open cap interval implies uniform derivative bounds on each compact interior band with clipped default value 1, stable under discount and stopping.
-- source:
--   Finite-cap Gaussian gbB58 uniform bound half, 11 November 2026.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB60_finitecap_clipped_gradient_uniform_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (δ : ℝ) (hδ : 0 < δ) (j : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (t : ℝ≥0) (ρ : Ω → ℝ≥0)
      (Y : Ω → ℝ) (ω : Ω),
      |if t < ρ ω then
        Real.exp (-(q * (t : ℝ))) *
          (if Y ω ∈ Icc (δ / 2)
            (C.toReal * (((j + 1 : ℕ) : ℝ) /
              ((j + 2 : ℕ) : ℝ))) then
              deriv w (Y ω) else 1)
      else 0| ≤ B := by sorry
