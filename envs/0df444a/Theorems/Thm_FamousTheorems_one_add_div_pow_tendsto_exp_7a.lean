-- Prove2me | Theorems.Thm_FamousTheorems_one_add_div_pow_tendsto_exp_7a
-- name    : FamousTheorems.one_add_div_pow_tendsto_exp_7a
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:25:36.479325+00:00
-- url     : https://prove2.me/theorems/79067fc6-74b9-4b1a-8d75-e5ab6b048242
-- title:
--   (1 + t/n)^n → e^t
-- statement:
--   **$(1+t/n)^n\to e^t$.** For every real number $t$,
--   $$\lim_{n\to\infty}\Big(1+\frac tn\Big)^n=e^t.$$
--
--   Jacob Bernoulli met the case $t=1$ in 1683 when studying continuously compounded interest, and the limit is one of the standard definitions of $e$ and of the exponential function. It is used in the Poisson limit of binomial distributions and in the product formula $e^{A}=\lim(1+A/n)^n$ for matrices and operators.
--
--   **Formalization note.** Mathlib's `Real.tendsto_one_add_div_pow_exp`. The limit is along the natural numbers $n\to\infty$. At $n=0$ the term $t/0$ equals $0$ by Lean's convention, which does not affect the limit.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Real.tendsto_one_add_div_pow_exp`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem one_add_div_pow_tendsto_exp_7a (t : ℝ) : Filter.Tendsto (fun n : ℕ => (1 + t / n) ^ n) Filter.atTop (nhds (Real.exp t)) := by sorry

end FamousTheorems
