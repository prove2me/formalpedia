-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_esscher_positive_tail_kernel_diverges_of_infinite_activity
-- name    : AvramDividend.Classical.bv_esscher_positive_tail_kernel_diverges_of_infinite_activity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T09:55:50.90937+00:00
-- url     : https://prove2.me/theorems/7ba11b21-4b2e-4a31-ae7f-6c59b31eb130
-- title:
--   Standing BV infinite activity forces canonical Esscher kernel divergence without extra assumptions
-- statement:
--   For a standing bounded-variation spectrally negative Lévy process with q>0, positive Esscher root and infinite negative-jump activity, construct the canonical continuous nonnegative integrable Esscher renewal kernel and prove it diverges at the origin. All moment and truncation assumptions come from the process's own ν_integrable field, with no extra mathematical hypotheses. It directly prepares the canonical scale zero-right derivative theorem.
-- source:
--   Proved bv_esscher_positive_tail_kernel_diverges_of_levy_activity (c1045080), built-in SpectrallyNegativeLevy.ν_integrable, and ENNReal.lt_top_iff_ne_top.

import Theorems.Thm_AvramDividend_Classical_bv_esscher_positive_tail_kernel_diverges_of_levy_activity
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Order.Filter.AtTopBot.Defs

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace AvramDividend.Classical

/-- Infinite negative activity supplies a diverging canonical Esscher kernel under only standing BV assumptions. -/
theorem bv_esscher_positive_tail_kernel_diverges_of_infinite_activity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hbv : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (hInfinite : ¬ X.ν (Iio (0 : ℝ)) < ⊤) :
    ∃ κ : ℝ → ℝ,
      (∀ t : ℝ, κ t = if 0 < t then
        ENNReal.toReal (((X.ν.map (fun y : ℝ => Real.toNNReal (-y))).withDensity
          (fun z : ℝ≥0 => ENNReal.ofReal (Real.exp (-(φ * (z : ℝ))))))
          {z : ℝ≥0 | t < (z : ℝ)}) else 0) ∧
      ContinuousOn κ (Ioi (0 : ℝ)) ∧
      AntitoneOn κ (Ioi (0 : ℝ)) ∧
      (∀ t : ℝ, t ≤ 0 → κ t = 0) ∧
      (∀ t : ℝ, 0 ≤ κ t) ∧
      IntegrableOn κ (Ioi (0 : ℝ)) volume ∧
      Tendsto κ (nhdsWithin (0 : ℝ) (Ioi 0)) atTop := by sorry

end AvramDividend.Classical
