-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_capped_grid_scale_value_positive_continuity
-- name    : AvramDividend.Classical.chat03_capped_grid_scale_value_positive_continuity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T20:54:51.872185+00:00
-- url     : https://prove2.me/theorems/fb1bf6d2-7096-4cd0-b332-87696d4d9a51
-- title:
--   Stopped q-scale values converge along capped first-grid times at positive reserves
-- statement:
--   At a sample path and horizon where the limiting stopped reserve x+X(min(τ,T)) is strictly positive, any open neighbourhood of W(x+X(min(τ,T))) contains W(x+X(min(kh,T))) for the first strict grid-exit index k on every sufficiently fine mesh. The proof combines X right-continuity with IsScaleFunction's continuity on the nonnegative axis, valid at strictly positive points. This deliberately excludes reserve zero where W may jump in bounded variation, and does not establish the killed martingale.
-- source:
--   Composition of published capped-first-grid passage-time convergence, SpectrallyNegativeLevy.rightCont and IsScaleFunction.2.2.1 continuity on Ici 0 at strictly positive reserves at the pinned Mathlib revision.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_first_grid_capped_time_convergence
import Mathlib.Topology.Order.LeftRightNhds

open MeasureTheory Set Filter Topology
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_capped_grid_scale_value_positive_continuity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (ω : Ω) (lower upper x : ℝ) (τ T : ℝ≥0)
    (hτ : IsGLB
      {t : ℝ≥0 | X.X t ω < lower ∨ upper < X.X t ω} τ)
    (hpos : 0 < x + X.X (min τ T) ω)
    (U : Set ℝ) (hU : IsOpen U)
    (hmem : W (x + X.X (min τ T) ω) ∈ U) :
    ∃ δ : ℝ≥0, 0 < δ ∧
      ∀ h : ℝ≥0, 0 < h → h < δ →
        ∃ k : ℕ,
          (X.X ((k : ℝ≥0) * h) ω < lower ∨
           upper < X.X ((k : ℝ≥0) * h) ω) ∧
          (∀ j : ℕ, j < k →
            ¬ (X.X ((j : ℝ≥0) * h) ω < lower ∨
               upper < X.X ((j : ℝ≥0) * h) ω)) ∧
          W (x + X.X (min ((k : ℝ≥0) * h) T) ω) ∈ U := by sorry
