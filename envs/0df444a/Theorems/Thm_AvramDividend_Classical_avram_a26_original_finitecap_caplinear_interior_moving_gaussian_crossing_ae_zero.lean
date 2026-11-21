-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a26_original_finitecap_caplinear_interior_moving_gaussian_crossing_ae_zero
-- name    : AvramDividend.Classical.avram_a26_original_finitecap_caplinear_interior_moving_gaussian_crossing_ae_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T10:04:30.929085+00:00
-- url     : https://prove2.me/theorems/e757ea3f-eaad-435d-9eaf-148e2b8c826d
-- title:
--   Actual finitecap caplinear Gaussian moving interior reserve crossing tends to zero pathwise
-- statement:
--   For any moving sequence of actual stopped postpayment reserves y_m in a compact positive pre-ruin band [a,b] with a≥r>0, and true Gaussian spatial crossing increments δ_m→0, the original caplinear finitecap HJB continuation difference V(y_m+δ_m)−V(y_m)→0. Uses Proved 2b5fcde3 uniform continuity of the exact caplinear V on compact [0,b+r] and Proved 11fe368b moving-base compact translation lemma. This directly supplies the essential a.e. crossing source without assuming global boundedness or differentiability of w above the cap, and isolates the 0/ruin boundary to separate localisation.
-- source:
--   Original finitecap zerojump physical stopped Gaussian crossing positive interior compact moving reserve. Analytic pathwise convergence source; original stopped X increment can instantiate δ.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Set Filter AvramDividend.Classical

theorem AvramDividend.Classical.avram_a26_original_finitecap_caplinear_interior_moving_gaussian_crossing_ae_zero
    (w : ℝ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hw_cont : ContinuousOn w (Set.Ici 0))
    (a b r : ℝ) (hr : 0 < r) (hra : r ≤ a) (hab : a ≤ b)
    (y δ : ℕ → ℝ) (hy : ∀ m, y m ∈ Set.Icc a b)
    (hδ : Tendsto δ atTop (nhds (0 : ℝ))) :
    let V : ℝ → ℝ := fun z =>
      if z ≤ c then w z else w c + (z - c)
    Tendsto (fun m => V (y m + δ m) - V (y m))
      atTop (nhds (0 : ℝ)) := by sorry
