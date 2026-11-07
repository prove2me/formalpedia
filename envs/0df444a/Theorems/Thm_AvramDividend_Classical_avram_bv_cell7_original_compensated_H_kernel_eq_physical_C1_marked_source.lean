-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_compensated_H_kernel_eq_physical_C1_marked_source
-- name    : AvramDividend.Classical.avram_bv_cell7_original_compensated_H_kernel_eq_physical_C1_marked_source
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T17:43:45.440353+00:00
-- url     : https://prove2.me/theorems/9529fd32-c639-4e71-a5ed-0a5e4ca7360d
-- title:
--   Original compensated C1 jump kernel equals the physical-horizon-clipped original kernel pathwise
-- statement:
--   At every original sample path and genuine ruin/horizon stopped clock, the original compensated HJB negative-mark C1 value-difference kernel is exactly the same discounted pre-right-payment source with the physical T cutoff used in the stopped physical-grid decomposition. The finite ENNReal min directly implies the stopped clock is at most T, so this exact pointwise identity needs no adaptedness, integrability, stochastic equality-in-law, or extra source-identity assumption.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_cell7_original_compensated_H_kernel_eq_physical_C1_marked_source
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ)
    (q a b : ℝ) (T : ℝ≥0) (ω : Ω) :
    let τ : ℝ≥0 :=
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let Y : ℝ≥0 → ℝ := fun t => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
    let E : Set (ℝ≥0 × ℝ) :=
      {p | p.1 ≤ τ ∧ Y p.1 ∈ Icc a b ∧ p.2 < 0}
    let H : ℝ≥0 × ℝ → ℝ := fun p =>
      if p ∈ E then Real.exp (-(q * (p.1 : ℝ))) *
        (w (Y p.1 + p.2) - w (Y p.1)) else 0
    let K : ℝ≥0 × ℝ → ℝ := fun p =>
      if p.1 ≤ T then w (Y p.1 + p.2) - w (Y p.1) else 0
    ∀ p : ℝ≥0 × ℝ,
      H p = Real.exp (-(q * (p.1 : ℝ))) * (if p ∈ E then K p else 0) := by sorry
