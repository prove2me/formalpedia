-- Prove2me | Theorems.Thm_CountingLLL_ReciprocalTest_source_parameter_bounds
-- name    : CountingLLL.ReciprocalTest.source_parameter_bounds
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T06:46:22.922703+00:00
-- url     : https://prove2.me/theorems/416eb116-af7e-4b62-bb22-faf41ea8162c
-- title:
--   ReciprocalTest contracted-walk parameter bounds
-- statement:
--   Under the hypothesis $e^{-3/10}\le B\le1$ of Lemma 6.5, put $u=2(1-B)/(2-B)$ and $\theta=u^2/(1-u+u^2)$. Then $0\le u<33/80$ and $0\le\theta<9/40$. These are the explicit bounds used in the analysis of Algorithm 6.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC 2027 #442, proof of Lemma 6.5, PDF p. 27, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Mathlib

theorem CountingLLL.ReciprocalTest.source_parameter_bounds (B : ℝ) (hB : Real.exp (-(3/10 : ℝ)) ≤ B) (hB1 : B ≤ 1) :
    let u := 2*(1-B)/(2-B)
    let θ := u^2/(1-u+u^2)
    0 ≤ u ∧ u < 33/80 ∧ 0 ≤ θ ∧ θ < 9/40 := by sorry
