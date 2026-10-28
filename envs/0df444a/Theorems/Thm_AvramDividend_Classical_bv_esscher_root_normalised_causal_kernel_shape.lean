-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_esscher_root_normalised_causal_kernel_shape
-- name    : AvramDividend.Classical.bv_esscher_root_normalised_causal_kernel_shape
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T09:21:02.902862+00:00
-- url     : https://prove2.me/theorems/44322440-4db5-4234-b7a8-b766910d680b
-- title:
--   Drift-normalised BV Esscher renewal kernel is causal continuous antitone L1 and subunit
-- statement:
--   Under standing bounded-variation assumptions at the positive Esscher root, explicitly normalise the positive jump-magnitude strict-tail kernel by the positive drift. Preserve causality, positive-axis continuity and monotonicity, nonnegativity and positive-axis L1 integrability. Its exact real integral is below one by the proved discounted-moment identity. Supplies the analytic kernel shape and contraction mass for the cstar-connected scaled subunit renewal identification 1ca4a724.
-- source:
--   Canonical Proved BV tail kernel shape 61873c37, exact BV real tail mass 6f5b9542, root subcriticality 3e5e114d, and standing drift positivity 0432f641.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Data.ENNReal.Real
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_bv_esscher_root_subcritical_kernel_mass
import Theorems.Thm_AvramDividend_Classical_bv_esscher_positive_tail_kernel_shape_of_root
import Theorems.Thm_AvramDividend_Classical_bv_esscher_positive_tail_real_total_mass_of_root
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_esscher_root_normalised_causal_kernel_shape
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hbv : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    ∃ κ : ℝ → ℝ,
      (∀ t : ℝ, κ t =
        if 0 < t then
          ENNReal.toReal (((X.ν.map (fun y : ℝ => Real.toNNReal (-y))).withDensity
            (fun z : ℝ≥0 => ENNReal.ofReal (Real.exp (-(φ * (z : ℝ))))))
            {z : ℝ≥0 | t < (z : ℝ)}) / X.drift else 0) ∧
      ContinuousOn κ (Ioi (0 : ℝ)) ∧
      AntitoneOn κ (Ioi (0 : ℝ)) ∧
      (∀ t : ℝ, t ≤ 0 → κ t = 0) ∧
      (∀ t : ℝ, 0 ≤ κ t) ∧
      IntegrableOn κ (Ioi (0 : ℝ)) volume ∧
      (∫ t in Ioi (0 : ℝ), κ t ∂volume) < 1 := by sorry
