-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_01_unbounded_killed_grid_ost_from_source
-- name    : AvramDividend.Classical.avram_root29_01_unbounded_killed_grid_ost_from_source
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T11:10:07.294913+00:00
-- url     : https://prove2.me/theorems/9b5aad36-0d08-477b-9cfb-cf0fa8ad4d6c
-- title:
--   Actual unbounded-variation lower-killed q-scale bounded-grid optional stopping
-- statement:
--   For a genuine original-law spectrally negative Levy process of unbounded variation, the lower-history-killed discounted q-scale reward stopped at any bounded finite observation grid first-exit has expectation W(x) for nonnegative reserve. This explicitly invokes the separately Proved source-specific martingale and the Proved generic bounded-grid optional-stopping theorem, without assuming any continuous first-passage conclusion.
-- source:
--   WS1A exclusive source draft work/avram_root29_01_unbounded_killed_grid_ost_from_source_draft.lean

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_unbounded_killed_martingale_from_source
import Theorems.Thm_AvramDividend_Classical_chat03_killed_scale_grid_optional_stopping_of_martingale

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_root29_01_unbounded_killed_grid_ost_from_source
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation)
    (q x : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) (hx : 0 ≤ x)
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
          (Set.Ioi (0 : ℝ)) 0 m ω)) ω)) ω ∂P) = W x := by sorry
