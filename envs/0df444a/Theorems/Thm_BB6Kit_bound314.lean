-- Prove2me | Theorems.Thm_BB6Kit_bound314
-- name    : BB6Kit.bound314
-- status  : Proved
-- author  : @alon yuval
-- created : 2026-11-24T07:20:41.213778+00:00
-- url     : https://prove2.me/theorems/fc990ca2-d9a0-4f47-a1ce-bc7b357fc0f0
-- title:
--   Numerical bound behind (3.14): $\rho K(K+1)L\,\rho^{-KL}/8\le 0.001$
-- statement:
--   **Lemma.** For integers $K\ge3$, $L\ge5$ and real $\rho\ge2$, $$\frac{\rho K(K+1)L}{8\,\rho^{KL}}\le 0.001.$$
--
--   This is the numerical estimate in (3.14) of the Mignotte–Voutier kit. With $\Lambda'<\rho^{-KL}$ it gives $\rho G_3|\Lambda|/b_3<0.001$. The left side decreases in $\rho$, $K$ and $L$, and at $K=3$, $L=5$, $\rho=2$ it equals $60/2^{17}<0.0005$.
-- source:
--   Mignotte & Voutier (appendix by Laurent), A kit for linear forms in three logarithms, Math. Comp. (2023), arXiv:2205.08899, proof of Proposition 3.7, eq. (3.14).

import Mathlib

namespace BB6Kit
theorem bound314 (K L : ℕ) (ρ : ℝ) (hK : 3 ≤ K) (hL : 5 ≤ L) (hρ : 2 ≤ ρ) :
    ρ * ((K : ℝ) * ((K : ℝ) + 1) * L) / 8 * ρ ^ (-((K : ℝ) * L)) ≤ 0.001 := by
  sorry
end BB6Kit
