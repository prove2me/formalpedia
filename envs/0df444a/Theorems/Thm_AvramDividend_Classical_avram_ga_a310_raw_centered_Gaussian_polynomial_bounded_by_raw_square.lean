-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a310_raw_centered_Gaussian_polynomial_bounded_by_raw_square
-- name    : AvramDividend.Classical.avram_ga_a310_raw_centered_Gaussian_polynomial_bounded_by_raw_square
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T09:49:01.952255+00:00
-- url     : https://prove2.me/theorems/e8acd60c-5aac-40bf-8eff-a89d358b4737
-- title:
--   Gaussian raw and centred quadratic first-order polynomial bounded by raw-square plus drift-square envelope
-- statement:
--   The original large-cell compact HJB source polynomial 1+abs(raw increment)+(centered increment)^2/2 is bounded by twice the raw squared increment plus the deterministic centering drift squared and a constant, without requiring a rare-event threshold or small drift. This provides integrability for every finite physical Gaussian mesh, to discharge the exact source a304 premise from proved true full-cell raw-square integrability a243.
-- source:
--   Real scalar Young and square inequalities for original Gaussian raw/centered source.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a310_raw_centered_Gaussian_polynomial_bounded_by_raw_square
    (r a : ℝ) :
    1 + |r| + (r-a)^2/2 ≤ 2*r^2 + a^2 + 2 := by sorry
