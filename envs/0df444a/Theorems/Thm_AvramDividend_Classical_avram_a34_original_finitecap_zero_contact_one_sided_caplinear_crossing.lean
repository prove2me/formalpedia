-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a34_original_finitecap_zero_contact_one_sided_caplinear_crossing
-- name    : AvramDividend.Classical.avram_a34_original_finitecap_zero_contact_one_sided_caplinear_crossing
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T16:06:06.819089+00:00
-- url     : https://prove2.me/theorems/15087883-4532-4e3f-bc8c-52de5dd078d4
-- title:
--   Actual finite-cap positive Gaussian spatial crossing vanishes even at zero reserve contact
-- statement:
--   The original finitecap caplinear continuation V has a possible upward discontinuity at reserve zero, because w(z)=0 below zero but w(0)>=0. Nevertheless, for every original postpayment reserve sequence y_m in the full closed physical band [0,b] and arbitrary Gaussian mesh increments delta_m to zero, the positive spatial increment max(V(y_m+delta_m)-V(y_m),0) tends to zero. Prove using the one-sided caplinear comparison with the continuous clamped extension V(max(z,0)), Proved compact caplinear uniform continuity gbB77, and Proved moving-base compact-translation convergence a32. This removes artificial strict-positive localisation at ruin contact and is a genuine missing finitecap original physical Gaussian source lemma.
-- source:
--   Original finitecap pre-ruin Gaussian spatial crossing positive-part convergence including zero-reserve terminal contact; nonnegative w(0) and zero-on-negative w are essential to one-sided conclusion.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Set Filter AvramDividend.Classical

theorem AvramDividend.Classical.avram_a34_original_finitecap_zero_contact_one_sided_caplinear_crossing
    (w : ℝ → ℝ) (b : ℝ) (hb : 0 ≤ b)
    (hw0 : 0 ≤ w 0)
    (hwneg : ∀ z : ℝ, z < 0 → w z = 0)
    (hwcont : ContinuousOn w (Set.Ici 0))
    (y δ : ℕ → ℝ)
    (hy : ∀ m, y m ∈ Set.Icc 0 b)
    (hδ : Tendsto δ atTop (nhds (0 : ℝ))) :
    let V : ℝ → ℝ := fun z =>
      if z ≤ b then w z else w b + (z - b)
    Tendsto (fun m => max (V (y m + δ m) - V (y m)) 0)
      atTop (nhds (0 : ℝ)) := by sorry
