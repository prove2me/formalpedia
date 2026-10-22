-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_tilt_contDiffOn_one_of_scale_contDiffOn_one
-- name    : AvramDividend.Classical.esscher_tilt_contDiffOn_one_of_scale_contDiffOn_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T22:34:06.929254+00:00
-- url     : https://prove2.me/theorems/bd041e71-a496-422e-9f34-2ba04edf69ed
-- title:
--   Continuous differentiability is preserved under exponential Esscher tilting
-- statement:
--   Let W be continuously differentiable on the positive real axis and define V there by V(x)=exp(-φx)W(x). Then V is continuously differentiable there, since its exponential multiplier is globally smooth. This deterministic lemma isolates the final calculus step needed after Gaussian or infinite-small-jump regularity of spectrally negative Lévy scale functions is established.
-- source:
--   Ordinary real multivariable calculus, closure of ContDiffOn under multiplication and composition, using Mathlib's ContDiff exponential properties.

import Mathlib
open Set

theorem AvramDividend.Classical.esscher_tilt_contDiffOn_one_of_scale_contDiffOn_one
    (φ : ℝ) (W V : ℝ → ℝ)
    (hW : ContDiffOn ℝ 1 W (Ioi (0 : ℝ)))
    (hV : ∀ x : ℝ, 0 < x → V x = Real.exp (-(φ * x)) * W x) :
    ContDiffOn ℝ 1 V (Ioi (0 : ℝ)) := by sorry
