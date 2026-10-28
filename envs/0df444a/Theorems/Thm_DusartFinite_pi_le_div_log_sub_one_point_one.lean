-- Prove2me | Theorems.Thm_DusartFinite_pi_le_div_log_sub_one_point_one
-- name    : DusartFinite.pi_le_div_log_sub_one_point_one
-- status  : Proved
-- author  : @sthubbar
-- created : 2026-10-26T18:26:52.390817+00:00
-- url     : https://prove2.me/theorems/a1950733-7085-4b45-85f6-1e654ac4bebd
-- title:
--   Dusart's $\pi$ bound on $[60184, 2\cdot 10^6]$
-- statement:
--   For every real $x$ with $60184 \le x \le 2\cdot 10^6$, the number of primes up to $x$ satisfies $\pi(x) \le \dfrac{x}{\log x - 1.1}$, where $\log$ is the natural logarithm.
-- source:
--   P. Dusart, Estimates of some functions over primes without R.H., arXiv:1002.0442, Theorem 6.9, restricted to x ≤ 2·10^6

import Mathlib

namespace DusartFinite

theorem pi_le_div_log_sub_one_point_one {x : ℝ} (h1 : 60184 ≤ x) (h2 : x ≤ 2 * 10 ^ 6) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ x / (Real.log x - 1.1) := by
  sorry

end DusartFinite
