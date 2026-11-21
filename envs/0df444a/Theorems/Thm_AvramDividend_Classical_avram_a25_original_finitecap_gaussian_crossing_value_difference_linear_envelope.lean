-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a25_original_finitecap_gaussian_crossing_value_difference_linear_envelope
-- name    : AvramDividend.Classical.avram_a25_original_finitecap_gaussian_crossing_value_difference_linear_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T09:49:38.198199+00:00
-- url     : https://prove2.me/theorems/4d5d7a6f-bcb7-4812-9954-40ba60f5f14e
-- title:
--   True original finitecap caplinear Gaussian crossing increment has globally linear absolute envelope
-- statement:
--   For original bounded controlled reserve y in [0,b] and arbitrary true Gaussian Levy cell increment r, the original cap-linear postpayment spatial correction V(y+r)−w(y) is globally bounded in absolute value by a finite K+b+|r|. Derive K from the compact HJB value bound on [0,b] plus proved 0f403353 caplinear prepayment crossing envelope. This controls exact full or crossing spatial increments without assuming raw w smoothness above cap.
-- source:
--   Finitecap actual stopped Gaussian spatial crossing correction, before stochastic expectation; scalar caplinear value bound for physical Ito error.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Set AvramDividend.Classical

theorem AvramDividend.Classical.avram_a25_original_finitecap_gaussian_crossing_value_difference_linear_envelope
    (w : ℝ → ℝ) (b : ℝ) (hb : 0 ≤ b)
    (hw_cont : ContinuousOn w (Set.Ici 0))
    (hw_neg : ∀ z : ℝ, z < 0 → w z = 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y r : ℝ,
      0 ≤ y → y ≤ b →
      |(if y + r ≤ b then w (y + r)
         else w b + (y + r - b)) - w y| ≤ K + b + |r| := by sorry
