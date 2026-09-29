-- Prove2me | Theorems.Thm_Erdos142_leng_sah_sawhney
-- name    : Erdos142.leng_sah_sawhney
-- status  : Open
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:41:23.996479+00:00
-- url     : https://prove2.me/theorems/c7120a4b-1fbb-47dc-bb1b-551db4e9384a
-- title:
--   Leng–Sah–Sawhney (2024): $r_k(N) \ll N e^{-(\log\log N)^{c_k}}$ for $k \ge 5$
-- statement:
--   For every $k \ge 5$ there is a constant $c_k > 0$ such that, for all sufficiently large $N$,
--
--   $$r_k(N) \;\le\; N\,e^{-(\log\log N)^{c_k}} .$$
--
--   This is the bound of Leng, Sah and Sawhney, the best known for progressions of length five and beyond. It improves Gowers's $r_k(N) \ll N(\log\log N)^{-c_k}$ by replacing a fixed negative power of $\log\log N$ with an exponential in a positive power of it.
--
--   The result is a consequence of quasipolynomial bounds in the inverse theorem for the Gowers $U^{k-1}$-norm, combined with the density increment strategy of Heath-Brown and Szemerédi in the form reorganised by Green and Tao. It marks the current quantitative ceiling for general $k$, and the distance from the goal of this mission is stark: $N e^{-(\log\log N)^{c}}$ is far larger than $N/\log N$, so the goal is not merely unproved for $k \ge 4$ but out of reach of the present technique.
--
--   **Formalization Note.** The implied constant of $\ll$ is absorbed by shrinking the exponent $c$, so the displayed form with $\exists c > 0$ and an eventual inequality is equivalent to the paper's statement.
-- source:
--   J. Leng, A. Sah and M. Sawhney, Improved bounds for Szemeredi's theorem, arXiv:2402.17995, https://arxiv.org/abs/2402.17995 (for k >= 5 there is c_k > 0 with r_k(N) << N exp(-(log log N)^{c_k})). Cited as the best known upper bound for k >= 5 on Erdős Problem #142, https://www.erdosproblems.com/142 (cited there as [Er80, p.92], [Er81, p.4], [Er97c], [Va99, 1.27])

import Mathlib
import Definitions.Def_Erdos142Basic

namespace Erdos142

theorem leng_sah_sawhney (k : ℕ) (hk : 5 ≤ k) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in Filter.atTop,
      (r k N : ℝ) ≤ (N : ℝ) * Real.exp (-(Real.log (Real.log N)) ^ c) := by sorry

end Erdos142
