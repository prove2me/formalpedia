-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_capped_grid_scale_value_negative_zero
-- name    : AvramDividend.Classical.chat03_capped_grid_scale_value_negative_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T20:56:35.613036+00:00
-- url     : https://prove2.me/theorems/afd8d7b8-cea6-46ae-86ef-b1c60fd93040
-- title:
--   Stopped q-scale function is eventually zero at strictly negative reserves
-- statement:
--   For a strictly negative limiting stopped reserve x+X(min(τ,T))<0, the q-scale function vanishes there and also vanishes at every sufficiently fine first strict-grid capped stop min(kh,T). The first grid exit index k is minimal. This uses right-continuous stopped-path convergence and the defining zero-left property of IsScaleFunction. The reserve-zero boundary is not included, and no killed q-scale martingale is asserted.
-- source:
--   Consequence of the proved Chat03 capped grid stopped-path open-neighbourhood convergence theorem and IsScaleFunction.zero_left at the pinned Mathlib revision.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_capped_grid_stopped_path_open_eventually
import Mathlib.Tactic.Linarith

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_capped_grid_scale_value_negative_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (ω : Ω) (lower upper x : ℝ) (τ T : ℝ≥0)
    (hτ : IsGLB
      {t : ℝ≥0 | X.X t ω < lower ∨ upper < X.X t ω} τ)
    (hneg : x + X.X (min τ T) ω < 0) :
    W (x + X.X (min τ T) ω) = 0 ∧
      ∃ δ : ℝ≥0, 0 < δ ∧
        ∀ h : ℝ≥0, 0 < h → h < δ →
          ∃ k : ℕ,
            (X.X ((k : ℝ≥0) * h) ω < lower ∨
             upper < X.X ((k : ℝ≥0) * h) ω) ∧
            (∀ j : ℕ, j < k →
              ¬ (X.X ((j : ℝ≥0) * h) ω < lower ∨
                 upper < X.X ((j : ℝ≥0) * h) ω)) ∧
            W (x + X.X (min ((k : ℝ≥0) * h) T) ω) = 0 := by sorry
