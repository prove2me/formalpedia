-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_discounted_C1_nonlinear_source_exact_stopped_clock_support
-- name    : AvramDividend.Classical.avram_bv_cell7_original_discounted_C1_nonlinear_source_exact_stopped_clock_support
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T17:24:30.274261+00:00
-- url     : https://prove2.me/theorems/ecc0e1df-90e8-464a-8281-bd77fafd33e6
-- title:
--   Original discounted compact C1 marked jump kernel vanishes beyond the actual ruin/horizon stop
-- statement:
--   The actual original pre-right-payment reserve C1 nonlinear negative-jump kernel, with its built-in ruin and physical-horizon indicators, is exactly zero beyond the smaller original stopped clock for every sample path and every jump mark. A direct elementary proof establishes the support needed to remove the global measure's time indicator, without a probabilistic or integrability assumption.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_cell7_original_discounted_C1_nonlinear_source_exact_stopped_clock_support
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (q c a b : ℝ) (T : ℝ≥0) (ω : Ω) :
    let τ : ℝ≥0 :=
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let Y : ℝ≥0 → ℝ := fun t => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
    let E : Set (ℝ≥0 × ℝ) :=
      {p | p.1 ≤ τ ∧ Y p.1 ∈ Icc a b ∧ p.2 < 0}
    let K : ℝ≥0 × ℝ → ℝ := fun p =>
      if p.1 ≤ T then w (Y p.1 + p.2) - w (Y p.1) else 0
    let F : ℝ≥0 × ℝ → ℝ≥0∞ := fun p =>
      ENNReal.ofReal (c * Real.exp (-(q * (p.1 : ℝ))) *
        (if p ∈ E then K p else 0))
    ∀ p : ℝ≥0 × ℝ, min T τ < p.1 → F p = 0 := by sorry
