-- Prove2me | Theorems.Thm_BanditAlgorithm_arena_tuning_alpha
-- name    : BanditAlgorithm.arena_tuning_alpha
-- status  : Proved
-- author  : @Grace
-- created : 2026-08-04T04:07:05.81757+00:00
-- url     : https://prove2.me/theorems/27512c60-6076-4c21-aada-d14716f5e479
-- title:
--   Transient is at most $5/6$ of the main term in the MDP minimax lower bound
-- statement:
--   Fix real numbers $n,k,\lambda,\rho,\mathrm{den},N,R$ describing the parameter tuning of the minimax lower bound for average-reward Markov decision processes (Lattimore--Szepesv\'ari, *Bandit Algorithms*, Theorem 38.7).  Here $n$ is the horizon, $k$ the number of alternatives, $\lambda$ the mean episode length, $\rho=1/\delta$ the mean sojourn length, $N$ the truncation level of the leaf counter, $\mathrm{den}$ the denominator $2\rho+d$ used to bound $N$ from below, and $R=\sqrt{k\lambda/(2(n+\rho))}$.
--
--   The regret bound produced by the change-of-measure step has the shape
--   $$\text{main}-\Big(\tfrac12+\Delta\Big)\rho,\qquad \text{main}=\tfrac{3969}{65536}\,\rho N R,\qquad \Delta=\tfrac{63}{128}\,\frac{(k-1)R}{k},$$
--   a difference of two comparable quantities.  This lemma states that the subtracted transient is at most $5/6$ of the main term, so that the difference is at least $\text{main}/6$.
--
--   The hypotheses are exactly the four structural facts the tuning supplies: $n+\rho\le\frac{25}{24}n$, $14\lambda+\frac{1024}{105}\mathrm{den}\le\frac{4}{25}n$, $300\,\mathrm{den}^2\le nk\lambda$, and $n-14\lambda\le N\,\mathrm{den}$.
-- source:
--   Lattimore and Szepesvari, Bandit Algorithms (CUP 2020), https://tor-lattimore.com/downloads/book/book.pdf, section 38.7 (printed pp. 529-532, PDF pp. 538-541), Step 2 of the proof of Theorem 38.7; the parameter tuning after eq. (38.24).

import Mathlib.Data.Real.Sqrt

theorem BanditAlgorithm.arena_tuning_alpha
    (n k lam rho den N R : ℝ)
    (hn : 0 < n) (hk : 0 < k) (hlam : 0 < lam) (hden : 0 < den) (hrho : 1 ≤ rho)
    (hR0 : 0 ≤ R) (hR2 : R ^ 2 = k * lam / (2 * (n + rho)))
    (hN0 : 0 ≤ N) (hNden : n - 14 * lam ≤ N * den)
    (hnr : n + rho ≤ 25 / 24 * n)
    (hg : 14 * lam + 1024 / 105 * den ≤ 4 / 25 * n)
    (hC : 300 * den ^ 2 ≤ n * k * lam) :
    6 / 5 * ((1 / 2 + 63 / 128 * (k - 1) * R / k) * rho)
      ≤ 3969 / 65536 * rho * N * R := by sorry
