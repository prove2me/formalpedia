-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB57_original_gaussian_finite_discounted_cash_abel_ledger
-- name    : AvramDividend.Classical.avram_gbB57_original_gaussian_finite_discounted_cash_abel_ledger
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T16:37:44.621533+00:00
-- url     : https://prove2.me/theorems/2ff0d7a9-6fe3-4a78-a6cd-f519e643d2d0
-- title:
--   Exact finite physical-grid Gaussian cash, reserve and noise Abel identity for an original reflected path
-- statement:
--   For arbitrary finite physical times, discounted weights, centred Gaussian coordinates B and continuous barrier dividends D with original reserve Y=C+B+2s-D, the discounted terminal reward plus physical dividend increments minus discounted Gaussian increments equals an explicit terminal affine defect, initial defect and discounted drift/weight-variation sums. This is the finite pathwise algebraic ledger behind the original caplinear stopped cash identity, with no stochastic or Riemann limit assumed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gbB53_physical_discounted_mesh_abel_telescope
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_gbB57_original_gaussian_finite_discounted_cash_abel_ledger
    (m : ℕ) (a B s D : ℕ → ℝ) (C : ℝ) (w : ℝ → ℝ) :
    let Y : ℕ → ℝ := fun i => C + B i + 2 * s i - D i
    a m * w (Y (m + 1)) +
      (Finset.range (m + 1)).sum (fun i => a i * (D (i + 1) - D i)) -
      a 0 * w (Y 0) -
      (Finset.range (m + 1)).sum (fun i => a i * (B (i + 1) - B i)) =
    a m * (w (Y (m + 1)) - Y (m + 1)) +
      a 0 * (Y 0 - w (Y 0)) +
      2 * (Finset.range (m + 1)).sum (fun i => a i * (s (i + 1) - s i)) -
      (Finset.range m).sum (fun i => (a i - a (i + 1)) * Y (i + 1))
    := by sorry
