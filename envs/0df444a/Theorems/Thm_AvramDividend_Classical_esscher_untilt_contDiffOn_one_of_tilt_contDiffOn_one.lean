-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_untilt_contDiffOn_one_of_tilt_contDiffOn_one
-- name    : AvramDividend.Classical.esscher_untilt_contDiffOn_one_of_tilt_contDiffOn_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T22:46:24.341287+00:00
-- url     : https://prove2.me/theorems/04e954e6-31ee-444b-8dcf-a0cb967c5881
-- title:
--   Recovering C1 scale smoothness from C1 Esscher tilted scale
-- statement:
--   If the Esscher-tilted function V(x) = e^{-phi x}W(x) is continuously differentiable on x>0, then W is continuously differentiable on x>0, since W(x)=e^{phi x}V(x). This is an independent elementary calculus lemma useful after a probabilistic proof of tilted-scale regularity.
-- source:
--   Mathlib Analysis Calculus ContDiff, composition and multiplication of C1 functions; exponential cancellation for the Esscher transform.

import Mathlib
open Set

theorem AvramDividend.Classical.esscher_untilt_contDiffOn_one_of_tilt_contDiffOn_one
    (φ : ℝ) (W V : ℝ → ℝ)
    (hVdiff : ContDiffOn ℝ 1 V (Ioi (0 : ℝ)))
    (hV : ∀ x : ℝ, 0 < x → V x = Real.exp (-(φ * x)) * W x) :
    ContDiffOn ℝ 1 W (Ioi (0 : ℝ)) := by sorry
