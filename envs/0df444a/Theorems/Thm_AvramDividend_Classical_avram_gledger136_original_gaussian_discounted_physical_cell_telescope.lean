-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger136_original_gaussian_discounted_physical_cell_telescope
-- name    : AvramDividend.Classical.avram_gledger136_original_gaussian_discounted_physical_cell_telescope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T18:35:13.902214+00:00
-- url     : https://prove2.me/theorems/2614a785-dde2-409a-abbb-2475bae468f2
-- title:
--   Physical Gaussian discounted time and reserve cell increments rebracket exactly
-- statement:
--   For the original Gaussian Taylor stopped mesh, the discount variation and physical prepayment reserve-value variation combine exactly into a discounted endpoint-value difference. The identity is purely algebraic and preserves the actual source times, reserves and postpayment value when instantiated in the original S mesh.
-- source:
--   Necessary exact cell rebracketing of the original S from avram_gledger50_original_clipped_gaussian_physical_Taylor_L1, with the same E and w; intended to be imported in a root-connected Gaussian Taylor reduction.

import Mathlib
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger136_original_gaussian_discounted_physical_cell_telescope
    (q : ℝ) (w : ℝ → ℝ) (s t : ℝ≥0) (y z : ℝ) :
    (Real.exp (-(q * (t : ℝ))) - Real.exp (-(q * (s : ℝ)))) * w y +
    Real.exp (-(q * (t : ℝ))) * (w z - w y) =
    Real.exp (-(q * (t : ℝ))) * w z -
    Real.exp (-(q * (s : ℝ))) * w y := by sorry
