-- Prove2me | Theorems.Thm_CountingLLL_RandomRAM_expected_offspring_reduction
-- name    : CountingLLL.RandomRAM.expected_offspring_reduction
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T06:09:27.777388+00:00
-- url     : https://prove2.me/theorems/88eaaea9-3e41-4457-8954-8d1dd06290f0
-- title:
--   Subcritical offspring from exploration and reciprocal bounds
-- statement:
--   Under the counting-and-sampling LLL condition, suppose the expected exploration tree size z is at most p_0/(1-pD^2), with 0<=p_0<=p. Suppose the sum of probabilities of active recursive slots is at most (D+1)^2 z, and the expected number of recursive calls arising from each slot is at most its activation probability divided by 1-p. Then the total expected number of recursive calls is at most beta=p(D+1)^2/((1-p)(1-pD^2)), which is below 1/8. This is the numerical reduction in the proof of Lemma 5.7; the adaptive conditional slot and tree bounds must still be established for Algorithm 2.
-- source:
--   Liu, Wang, Yin, Zhang, Zhou, A Counting and Sampling Lovasz Local Lemma, STOC submission #442, proof of Lemma 5.7, Section 5.2.3, PDF p.20, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Mathlib
open scoped BigOperators

theorem CountingLLL.RandomRAM.expected_offspring_reduction {ι : Type} [Fintype ι] (p p0 D z : ℝ) (active children : ι → ℝ)
    (hp : 0 ≤ p) (hp0 : 0 ≤ p0) (hp0p : p0 ≤ p) (hD : 1 ≤ D)
    (hcondition : 4 * Real.exp 1 * p * (D+1)^2 ≤ 1)
    (htree : z ≤ p0 / (1-p*D^2))
    (hslots : (∑ i, active i) ≤ (D+1)^2 * z)
    (hchild : ∀ i, children i ≤ active i / (1-p)) :
    (∑ i, children i) ≤ p * (D+1)^2 / ((1-p)*(1-p*D^2)) ∧
    (∑ i, children i) < 1/8 := by sorry
