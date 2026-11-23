-- Prove2me | Theorems.Thm_BB6Baker_numerics
-- name    : BB6Baker.numerics
-- status  : Proved
-- author  : @alon yuval
-- created : 2026-11-23T17:55:57.503299+00:00
-- url     : https://prove2.me/theorems/86e1961c-416f-4036-a170-b6dea562bd8d
-- title:
--   Numeric inequality: $\log(i+5) + 2^{42}\log(2i+2)\log 3\log(4i) < i\log 3$ for $i \ge 2^{60}$
-- statement:
--   **Theorem.** For every integer $i \ge 2^{60}$, $$\log(i+5) + 2^{42}\,\log(2i+2)\,\log 3\,\log(4i) < i\log 3.$$
--
--   An elementary estimate (e.g. via $\log x \le x^{\varepsilon}/\varepsilon$). It is the numeric step converting the Baker-type bound `BB6Baker.bw_instance` into the Pillai gap `BB6Baker.pillai_gap`.
-- source:
--   rwst/bbchallenge (CC0), 1RB1LA_1RC1RE_1LD0RB_1LA0LC_0RF0RD_0RB---/BakerWustholz.lean and Ellison.lean; Baker & Wüstholz, J. reine angew. Math. 442 (1993) 19–62.

import Mathlib

namespace BB6Baker
theorem numerics (i : ℕ) (hi : 2 ^ 60 ≤ i) :
    Real.log ((i : ℝ) + 5) + 2 ^ 42 * Real.log (2 * (i : ℝ) + 2) * Real.log 3 * Real.log (4 * (i : ℝ)) <
      (i : ℝ) * Real.log 3 := by
  sorry
end BB6Baker
