-- Prove2me | Theorems.Thm_CountingLLL_ReciprocalTest_source_accuracy_algebra
-- name    : CountingLLL.ReciprocalTest.source_accuracy_algebra
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T07:15:14.017197+00:00
-- url     : https://prove2.me/theorems/988fc0e2-1597-4614-b5de-c17b1a9ca9ed
-- title:
--   ReciprocalTest final output-probability calculation
-- statement:
--   For $0<B<1$, define $u=2(1-B)/(2-B)$, $\theta=u^2/(1-u+u^2)$, and $I=1-\theta/(2(1-\theta))$. Then the expression for the output-one probability obtained from the paper’s generating-function and integral identities equals $1/(2B)$. This verifies their final algebraic calculation; the stochastic generating-function identities themselves remain to be proved.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC 2027 #442, proof of Lemma 6.5, PDF p. 27, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Mathlib

theorem CountingLLL.ReciprocalTest.source_accuracy_algebra (B : ℝ) (hB0 : 0 < B) (hB1 : B < 1) :
    let u := 2*(1-B)/(2-B)
    let θ := u^2/(1-u+u^2)
    let I := 1-θ/(2*(1-θ))
    1-((1-u)*I + u*(I-1+θ)/θ)/2 = 1/(2*B) := by sorry
