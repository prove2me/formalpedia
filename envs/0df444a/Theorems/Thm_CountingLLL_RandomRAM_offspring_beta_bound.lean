-- Prove2me | Theorems.Thm_CountingLLL_RandomRAM_offspring_beta_bound
-- name    : CountingLLL.RandomRAM.offspring_beta_bound
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T06:04:43.631391+00:00
-- url     : https://prove2.me/theorems/41b33521-24a4-4079-b682-43f807db937f
-- title:
--   Subcritical offspring constant under the counting LLL condition
-- statement:
--   For p>=0 and D>=1 satisfying 4 e p (D+1)^2<=1, the quantity beta=p(D+1)^2/((1-p)(1-pD^2)) is nonnegative, at most 40/351, and strictly below 1/8. This is the numerical subcriticality estimate in the proof of Lemma 5.7. It does not by itself establish that the adaptive randomized estimator has beta-bounded expected offspring.
-- source:
--   Liu, Wang, Yin, Zhang, Zhou, A Counting and Sampling Lovasz Local Lemma, STOC submission #442, proof of Lemma 5.7, Section 5.2.3, PDF p.20, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Mathlib

theorem CountingLLL.RandomRAM.offspring_beta_bound (p D : ℝ) (hp : 0 ≤ p) (hD : 1 ≤ D)
    (hcondition : 4 * Real.exp 1 * p * (D+1)^2 ≤ 1) :
    0 ≤ p * (D+1)^2 / ((1-p) * (1-p*D^2)) ∧
    p * (D+1)^2 / ((1-p) * (1-p*D^2)) ≤ 40/351 ∧
    p * (D+1)^2 / ((1-p) * (1-p*D^2)) < 1/8 := by sorry
