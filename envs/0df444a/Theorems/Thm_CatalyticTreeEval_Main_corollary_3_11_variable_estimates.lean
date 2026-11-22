-- Prove2me | Theorems.Thm_CatalyticTreeEval_Main_corollary_3_11_variable_estimates
-- name    : CatalyticTreeEval.Main.corollary_3_11_variable_estimates
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-22T23:23:55.852866+00:00
-- url     : https://prove2.me/theorems/f01860db-969a-464d-8a3d-b03b4f33a00f
-- title:
--   Appendix C, Item 2 — variable-prime parameter estimates
-- statement:
--   For the variable-prime regime, write $t=\lceil\sqrt{\log_2\ell}\rceil$ and let $p$ be the list of the first $t$ odd primes. Use the same Appendix C parameters $w,H,r,D$ as in the fixed-prime estimate.
--
--   There are absolute positive constants $C_d,C_s$ and an absolute integer threshold $L\ge2$ such that, for every $\ell\ge L$, one has $1\le w\le H$ and $\binom Hw\ge2^\ell$, the dimension estimate
--
--   $$
--   D\le 2^{2^{C_d\sqrt{\log_2\ell}}},
--   $$
--
--   and the workspace estimate
--
--   $$
--   1+\log_2\binom Hw+r\log_2(H+1)+\log_2m
--   \le C_s\bigl(\ell+\operatorname{lg}D+\operatorname{lg}m\bigr).
--   $$
--
--   The estimate packages Appendix C's use of the prime number theorem, its asymptotics for $\log\eta$, $\eta^{1/t}$, $\theta$, and $(mw)^{1/t}$, and its final absorption of these costs by $\ell$ beyond an absolute threshold.
-- source:
--   Alexandra Henzinger, Edward Pyne, Seyoon Ragavan, Catalytic Tree Evaluation from Matching Vectors, STOC 2027 submission #533 (October 2026), Appendix C, proof of Corollary 3.11, Item 2, printed p.40 (PDF p.42), including the prime-number-theorem and final asymptotic calculations.

import Definitions.Def_CatalyticTreeEval_Corollary311Parameters

set_option autoImplicit false

theorem CatalyticTreeEval.Main.corollary_3_11_variable_estimates :
    ∃ (Cd Cs : ℝ) (L : ℕ), 0 < Cd ∧ 0 < Cs ∧ 2 ≤ L ∧
      ∀ l : ℕ, L ≤ l →
        let p := firstOddPrimes (variablePrimeCount l)
        1 ≤ regimeWidth p l ∧ regimeWidth p l ≤ regimeHeight p l ∧
        2 ^ l ≤ (regimeHeight p l).choose (regimeWidth p l) ∧
        (regimeDimension p l : ℝ) ≤ exp₂ (exp₂ (Cd * Real.sqrt (log₂ l))) ∧
        regimeSpace p l ≤ Cs * (l + lg (regimeDimension p l) + lg (modulus p)) := by sorry
