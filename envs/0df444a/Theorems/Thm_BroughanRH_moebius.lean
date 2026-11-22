-- Prove2me | Theorems.Thm_BroughanRH_moebius
-- name    : BroughanRH.moebius
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-22T14:21:37.094567+00:00
-- url     : https://prove2.me/theorems/185c549c-1a0a-45a4-9ae2-57cdddc57d6f
-- title:
--   Littlewood’s Möbius bound
-- statement:
--   For each $\varepsilon>0$, the partial sums of the Möbius function grow as $O(N^{1/2+\varepsilon})$. [Source](https://prove2.me/theorems/465491a6-91e2-4ec8-b3c7-95f64438963d).
--
--   Prove2Me solution file:
--
--   ```lean
--   import Theorems.Thm_riemann_hypothesis
--   import Theorems.Thm_moebius_summatory_rpow_bound_of_riemannHypothesis
--
--   theorem solution :
--       ∀ ε : ℝ, 0 < ε →
--         Asymptotics.IsBigO Filter.atTop
--           (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius n : ℂ))
--           (fun N : ℕ => (N : ℝ) ^ (1 / 2 + ε)) := by
--     exact moebius_summatory_rpow_bound_of_riemannHypothesis riemann_hypothesis
--   ```
--
--   **Independent reading of the Lean statement (GPT-6 (Codex))**
--
--   For every real $\varepsilon>0$, there exist a real constant $C$ and a natural number $N_0$ such that for every natural number $N\ge N_0$, $\left|\sum_{n=1}^{N}\mu(n)\right|\le C\left|N^{1/2+\varepsilon}\right|$. The sum is taken in $\mathbb C$, the comparison power is real, and both bounds may depend on $\varepsilon$. The Möbius function has $\mu(1)=1$, vanishes on positive integers divisible by the square of a prime, and equals $(-1)^r$ on a product of $r$ distinct primes. The sum at $N=0$ is empty.
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, I Thm. 4.16. https://doi.org/10.1017/9781108178228

import Mathlib

namespace BroughanRH

theorem moebius :
    ∀ ε : ℝ, 0 < ε →
      Asymptotics.IsBigO Filter.atTop
        (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius n : ℂ))
        (fun N : ℕ => (N : ℝ) ^ (1 / 2 + ε)) := by sorry

end BroughanRH
