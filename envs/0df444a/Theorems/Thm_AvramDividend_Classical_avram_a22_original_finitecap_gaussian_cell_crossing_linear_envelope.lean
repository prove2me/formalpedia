-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a22_original_finitecap_gaussian_cell_crossing_linear_envelope
-- name    : AvramDividend.Classical.avram_a22_original_finitecap_gaussian_cell_crossing_linear_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T08:19:53.740397+00:00
-- url     : https://prove2.me/theorems/0f403353-bcfe-4876-b49a-0acf7336e077
-- title:
--   Original finitecap Gaussian prepayment cell caplinear value has uniform linear crossing bound
-- statement:
--   For every original postpayment controlled reserve y in the finite interval [0,b] and every real Gaussian Lévy increment r, the cap-linear continuation evaluated at the true prepayment intermediate reserve y+r has absolute value bounded uniformly by K+b+|r|, where K is independent of the cell, y and increment. This follows from original HJB continuity and the positive-cap caplinear global linear growth. It is the source bound needed to control a single stopped Gaussian crossing cell by integrable noise increments, without the false globally bounded uniformly continuous value assumption.
-- source:
--   Original capped postpayment reserve plus actual Gaussian spatial increment prepayment; caplinear growth source for stochastic crossing L1 UI.

import Mathlib
open Set

theorem AvramDividend.Classical.avram_a22_original_finitecap_gaussian_cell_crossing_linear_envelope
    (w : ℝ → ℝ) (b : ℝ) (hb : 0 ≤ b)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ z : ℝ, z < 0 → w z = 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y r : ℝ,
      0 ≤ y → y ≤ b →
      |if y + r ≤ b then w (y + r)
       else w b + (y + r - b)| ≤ K + b + |r| := by sorry
