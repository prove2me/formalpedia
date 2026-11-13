-- Prove2me | Theorems.Thm_CountingLLL_RandomRAM_marginal_variance_budget
-- name    : CountingLLL.RandomRAM.marginal_variance_budget
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T05:21:38.634914+00:00
-- url     : https://prove2.me/theorems/02ecef9f-0635-4179-9497-5e266dd1325f
-- title:
--   Relative variance budget under the counting LLL condition
-- statement:
--   Let r_i and v_i be nonnegative numbers, with r_i <= 1.2 p and v_i <= 3p/L. Assume p>=0, D>=1, L>0, epsilon>0, the counting and sampling condition 4 e p (D+1)^2 <= 1, and the sample-count bound L(D+1)^2 epsilon^2 >= 8m, where m is the number of indices. Then the sum of v_i/(1-r_i)^2 is at most epsilon^2/20. This is the numerical variance budget in the proof of equation (34); the probabilistic marginal-estimator bounds must be proved separately.
-- source:
--   Liu, Wang, Yin, Zhang, Zhou, A Counting and Sampling Lovasz Local Lemma, STOC submission #442, proof of Theorem 1.3, Section 5.3, equation (34), PDF pp.20-21, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Mathlib
open scoped BigOperators

theorem CountingLLL.RandomRAM.marginal_variance_budget {ι : Type} [Fintype ι]
    (r v : ι → ℝ) (p D L ε : ℝ)
    (hp : 0 ≤ p) (hD : 1 ≤ D) (hL : 0 < L) (he : 0 < ε)
    (hcondition : 4 * Real.exp 1 * p * (D + 1) ^ 2 ≤ 1)
    (hr0 : ∀ i, 0 ≤ r i) (hr : ∀ i, r i ≤ (6 / 5) * p)
    (hv0 : ∀ i, 0 ≤ v i) (hv : ∀ i, v i ≤ 3 * p / L)
    (hLbound : 8 * (Fintype.card ι : ℝ) ≤ L * (D + 1) ^ 2 * ε ^ 2) :
    (∑ i, v i / (1 - r i) ^ 2) ≤ ε ^ 2 / 20 := by sorry
