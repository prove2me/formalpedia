-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_untilt_contDiffOn_two_of_tilt_contDiffOn_two
-- name    : AvramDividend.Classical.esscher_untilt_contDiffOn_two_of_tilt_contDiffOn_two
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T21:07:26.703484+00:00
-- url     : https://prove2.me/theorems/c75b6edb-b30c-40c9-8c8d-ead2ec645117
-- title:
--   Recover C2 regularity after undoing an exponential Esscher tilt
-- statement:
--   If an exponentially Esscher-tilted real function V(x)=exp(-φx)W(x) on x>0 is twice continuously differentiable there, then W(x)=exp(φx)V(x) is also twice continuously differentiable. This isolates the final elementary calculus step for the Gaussian C2 scale-function regularity branch.
-- source:
--   Elementary closure of C2 functions under multiplication, applied to the Esscher transform of scale functions; Chan, Kyprianou and Savov (2011), Smoothness of scale functions for spectrally negative Lévy processes, Theorem 1, DOI 10.1007/s00440-010-0289-4.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FunProp

open Set

namespace AvramDividend.Classical

theorem esscher_untilt_contDiffOn_two_of_tilt_contDiffOn_two
    (φ : ℝ) (W V : ℝ → ℝ)
    (hVc : ContDiffOn ℝ 2 V (Ioi (0 : ℝ)))
    (hV : ∀ x : ℝ, 0 < x →
      V x = Real.exp (-(φ * x)) * W x) :
    ContDiffOn ℝ 2 W (Ioi (0 : ℝ)) := by sorry

end AvramDividend.Classical
