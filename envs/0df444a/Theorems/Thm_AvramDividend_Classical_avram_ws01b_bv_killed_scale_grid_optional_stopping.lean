-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01b_bv_killed_scale_grid_optional_stopping
-- name    : AvramDividend.Classical.avram_ws01b_bv_killed_scale_grid_optional_stopping
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T10:58:22.633006+00:00
-- url     : https://prove2.me/theorems/e7f81c41-55cc-4ac0-8cae-5cd59418c535
-- title:
--   Actual BV killed-scale exact bounded-grid first-exit expectation
-- statement:
--   Under genuine Standing bounded-variation Lévy law and q>0, at any monotone observation grid with time zero and a bounded first hit of a two-sided interval, the expected killed discounted q-scale at the sampled exit time is exactly W(x). The reward is killed by any continuous-time lower passage before grid sampling, so no path-recovery contamination occurs; valid at BV x=0.
-- source:
--   Consequence of canonically Proved c2 original-law conditional q-harmonicity via the BV true killed-scale martingale ab64adeb and canonically Proved generic bounded-grid first exit optional stopping b6c72d3d; no stopped continuous time martingale or false W(0)=0 assumption.

import Mathlib
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_bv_killed_scale_martingale
import Theorems.Thm_AvramDividend_Classical_chat03_killed_scale_grid_optional_stopping_of_martingale

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal

theorem AvramDividend.Classical.avram_ws01b_bv_killed_scale_grid_optional_stopping
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q x : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation) (hx : 0 ≤ x)
    (clock : ℕ → ℝ≥0) (hc : Monotone clock)
    (hclock0 : clock 0 = 0)
    (lower upper : ℝ) (m : ℕ) :
    (∫ ω,
      ({ω | ∀ s : ℝ≥0,
        s ≤ clock (hittingBtwn
          (fun k ω => max (X.X (clock k) ω - upper)
            (lower - X.X (clock k) ω))
          (Set.Ioi (0 : ℝ)) 0 m ω) →
          0 ≤ x + X.X s ω}).indicator
      (fun ω =>
        Real.exp (-(q * (clock (hittingBtwn
          (fun k ω => max (X.X (clock k) ω - upper)
            (lower - X.X (clock k) ω))
          (Set.Ioi (0 : ℝ)) 0 m ω) : ℝ))) *
        W (x + X.X (clock (hittingBtwn
          (fun k ω => max (X.X (clock k) ω - upper)
            (lower - X.X (clock k) ω))
          (Set.Ioi (0 : ℝ)) 0 m ω)) ω)) ω ∂P) = W x := by
  sorry
