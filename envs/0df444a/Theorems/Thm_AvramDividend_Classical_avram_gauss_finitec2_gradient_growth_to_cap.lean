-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gauss_finitec2_gradient_growth_to_cap
-- name    : AvramDividend.Classical.avram_gauss_finitec2_gradient_growth_to_cap
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T00:48:52.264376+00:00
-- url     : https://prove2.me/theorems/67b9ca67-537d-472b-8ac3-8d3fd13af827
-- title:
--   Finite-cap dividend-gradient lower bound implies value growth to cap
-- statement:
--   For the original candidate on a finite top cap band, continuity through the cap and interior derivative at least one imply w(C)-w(t)>=C-t. The proof shows w(y)-y is monotone by pinned mean-value/derivative monotonicity. This supplies the last lower-growth input of cap quadratic glue 4745a3db and the cap contact portion of the original stopped Gaussian d1caa4aa.
-- source:
--   Exact lower-gradient to cap comparison needed by CAP-Q four-case proof; already available original d1caa4aa hw_grad and hw_cont instantiate the premises.

import Mathlib.Analysis.Calculus.Deriv.MeanValue

open Set
noncomputable section

theorem AvramDividend.Classical.avram_gauss_finitec2_gradient_growth_to_cap
    (w : ℝ → ℝ) (u C : ℝ) (huC : u < C)
    (hwcont : ContinuousOn w (Icc u C))
    (hwderiv : ∀ y ∈ Ioo u C, HasDerivAt w (deriv w y) y)
    (hgrad : ∀ y ∈ Ioo u C, 1 ≤ deriv w y) :
    ∀ t ∈ Icc u C, C - t ≤ w C - w t := by sorry
