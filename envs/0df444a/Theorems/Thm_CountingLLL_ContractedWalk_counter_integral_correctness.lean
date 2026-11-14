-- Prove2me | Theorems.Thm_CountingLLL_ContractedWalk_counter_integral_correctness
-- name    : CountingLLL.ContractedWalk.counter_integral_correctness
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:20:43.619926+00:00
-- url     : https://prove2.me/theorems/e0ad1526-d10b-49c0-9307-18bdd7483cce
-- title:
--   Integrated contracted-counter output formula
-- statement:
--   For $e^{-3/10}\le B<1$, put $u=2(1-B)/(2-B)$ and $\theta=u^2/(1-u+u^2)$. The source’s contracted-counter generating function $H(z)=(1-u)G_\theta(z)+uzG_\theta(z)^3$ satisfies $1-\frac12\int_0^1H(z)\,dz=1/(2B)$. This verifies the integrated output formula in the abstract walk model; the correspondence with the full ReciprocalTest execution remains separate.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC 2027 #442, proof of Lemma 6.5, PDF pp. 27–28, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_ContractedGF
open MeasureTheory CountingLLL.ContractedWalk
open scoped Interval

theorem CountingLLL.ContractedWalk.counter_integral_correctness (B : ℝ) (hB0 : 0 < B) (hB1 : B < 1)
    (hB : Real.exp (-(3/10 : ℝ)) ≤ B) :
    let u := 2*(1-B)/(2-B)
    let θ := u^2/(1-u+u^2)
    1 - (∫ z in (0:ℝ)..1, ((1-u)*generatingFunction θ z + u*z*(generatingFunction θ z)^3))/2 = 1/(2*B) := by sorry
