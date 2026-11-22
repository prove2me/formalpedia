-- Prove2me | Theorems.Thm_CatalyticTreeEval_Main_corollary_3_11_fixed_estimates
-- name    : CatalyticTreeEval.Main.corollary_3_11_fixed_estimates
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-22T23:21:35.680473+00:00
-- url     : https://prove2.me/theorems/738ae11f-1396-4e13-af45-3055f37a0c76
-- title:
--   Appendix C, Item 1 — fixed-prime parameter estimates
-- statement:
--   Fix $t\ge2$ distinct odd primes, and use Appendix C's parameters $\eta=\ell^{t-1}/m$, $\theta=\max(10,\lceil(\log\eta)/t^2\rceil)$, $w=\lceil\ell/\theta\rceil$, $H=w2^\theta$, $r=(mw)^{1/t}$, and $D=\sum_{j=0}^{\lfloor r\rfloor}\binom Hj$.
--
--   There are positive constants $C_d,C_s$, depending only on the fixed primes, such that for every $\ell\ge1$ the parameters satisfy $1\le w\le H$ and $\binom Hw\ge2^\ell$, and
--
--   $$
--   D\le 2^{C_d\ell^{1/t}(\log_2(\ell+2))^{1-1/t}},
--   $$
--
--   together with the workspace estimate
--
--   $$
--   1+\log_2\binom Hw+r\log_2(H+1)+\log_2m
--   \le C_s\bigl(\ell+\operatorname{lg}D+\operatorname{lg}m\bigr).
--   $$
--
--   Here $\operatorname{lg}a=1+\log_2(a+1)$. This packages the fixed-prime asymptotic calculation in Appendix C, including absorption of the finitely many small values of $\ell$ into the constants.
-- source:
--   Alexandra Henzinger, Edward Pyne, Seyoon Ragavan, Catalytic Tree Evaluation from Matching Vectors, STOC 2027 submission #533 (October 2026), Appendix C, proof of Corollary 3.11, Item 1, printed pp.39-40 (PDF pp.41-42), equation (8) and the fixed-prime calculations.

import Definitions.Def_CatalyticTreeEval_Corollary311Parameters

set_option autoImplicit false

theorem CatalyticTreeEval.Main.corollary_3_11_fixed_estimates
    {t : ℕ} (p : Fin t → ℕ) (ht : 2 ≤ t) (hp : OddPrimeData p) :
    ∃ (Cd Cs : ℝ), 0 < Cd ∧ 0 < Cs ∧
      ∀ l : ℕ, 1 ≤ l →
        1 ≤ regimeWidth p l ∧ regimeWidth p l ≤ regimeHeight p l ∧
        2 ^ l ≤ (regimeHeight p l).choose (regimeWidth p l) ∧
        (regimeDimension p l : ℝ) ≤ exp₂
          (Cd * (l : ℝ) ^ (1 / (t : ℝ)) * (log₂ (l + 2)) ^ (1 - 1 / (t : ℝ))) ∧
        regimeSpace p l ≤ Cs * (l + lg (regimeDimension p l) + lg (modulus p)) := by sorry
