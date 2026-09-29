-- Prove2me | Theorems.Thm_Esgk_high_ratio_factor_exists
-- name    : Esgk.high_ratio_factor_exists
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-17T01:48:01.640402+00:00
-- url     : https://prove2.me/theorems/ca37b394-310c-45c8-80c9-9c206c404153
-- title:
--   A factor with high point-to-degree ratio exists
-- statement:
--   If point counts $N_i$ sum to $n \ge 1$ and degrees $d_i$ sum to at most $2s$, some index satisfies $d_i \le 2s$ and $n d_i \le N_i 2s$. This is the factor-selection step: some carrier factor has high point-to-degree ratio.
-- source:
--   esgk-on3 lean/Esgk/AdditiveExcessArithmetic.lean (Esgk.high_ratio_factor_exists)

import Mathlib

namespace Esgk

/-- Factor selection (§15, boxed (15.1)): from total counts and total
degree, some factor has high point-to-degree ratio. With `∑ N = n` and
`∑ d ≤ 2s`, some `i` satisfies `d i ≤ 2s` and `n * d i ≤ N i * (2s)`. -/
theorem high_ratio_factor_exists {ι : Type} [Fintype ι] [DecidableEq ι]
    (N d : ι → ℕ) (n s : ℕ) (hn : 1 ≤ n)
    (hN : ∑ i, N i = n) (hd : ∑ i, d i ≤ 2 * s) :
    ∃ i, d i ≤ 2 * s ∧ n * d i ≤ N i * (2 * s)  := by sorry

end Esgk
