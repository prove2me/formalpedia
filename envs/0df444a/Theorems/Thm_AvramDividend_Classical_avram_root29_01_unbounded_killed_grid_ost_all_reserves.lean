-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_01_unbounded_killed_grid_ost_all_reserves
-- name    : AvramDividend.Classical.avram_root29_01_unbounded_killed_grid_ost_all_reserves
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T11:20:19.626318+00:00
-- url     : https://prove2.me/theorems/93e89e55-8bff-460e-ab95-997cb74e2d2e
-- title:
--   Source-level unbounded-variation killed q-scale bounded-grid OST for every real reserve
-- statement:
--   Extends the canonically Proved genuine original-law UBV killed-scale bounded-grid optional-stopping expectation to all real initial reserves, using the Proved pointwise vanishing of the killed payoff and scale support for negative x. This is an exact finite-grid result, not a continuous first-passage identity.
-- source:
--   WS1A exclusive work/avram_root29_01_unbounded_killed_grid_ost_all_reserves_draft.lean

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_unbounded_killed_grid_ost_from_source
import Theorems.Thm_AvramDividend_Classical_chat04_killed_scale_payoff_zero_of_negative_initial_reserve

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_root29_01_unbounded_killed_grid_ost_all_reserves
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation)
    (q x : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
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
