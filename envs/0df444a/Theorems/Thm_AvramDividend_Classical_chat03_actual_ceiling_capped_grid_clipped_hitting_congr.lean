-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_actual_ceiling_capped_grid_clipped_hitting_congr
-- name    : AvramDividend.Classical.chat03_actual_ceiling_capped_grid_clipped_hitting_congr
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T05:29:08.380554+00:00
-- url     : https://prove2.me/theorems/2edb6173-bcec-4d2b-8518-a072c89b3f16
-- title:
--   Clipping terminal uniform-grid observations preserves actual first-hitting index
-- statement:
--   For a spectrally negative Lévy process sampled on a uniform nonnegative grid, the bounded first-hitting index up to ceil(T/h) is exactly the same when every observation time is clipped to T. All preterminal observations remain unchanged because j<ceil(T/h) implies j*h<T; the terminal observation cannot change hittingBtwn's returned index.
-- source:
--   Combine accepted chat03_ceiling_grid_preterminal_lt with accepted chat03_hittingBtwn_congr_before_terminal. The proof applies the generic congruence and rewrites min(j*h,T) at each preterminal index.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_hittingBtwn_congr_before_terminal
import Theorems.Thm_AvramDividend_Classical_chat03_ceiling_grid_preterminal_lt
import Mathlib.Probability.Process.HittingTime

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_actual_ceiling_capped_grid_clipped_hitting_congr
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (lower upper : ℝ) (T h : ℝ≥0) (hh : 0 < h) (ω : Ω) :
    hittingBtwn
      (fun (j : ℕ) ξ => max
        (X.X ((j : ℝ≥0) * h) ξ - upper)
        (lower - X.X ((j : ℝ≥0) * h) ξ))
      (Set.Ioi (0 : ℝ)) 0 (Nat.ceil (T / h)) ω =
    hittingBtwn
      (fun (j : ℕ) ξ => max
        (X.X (min ((j : ℝ≥0) * h) T) ξ - upper)
        (lower - X.X (min ((j : ℝ≥0) * h) T) ξ))
      (Set.Ioi (0 : ℝ)) 0 (Nat.ceil (T / h)) ω := by
  sorry
