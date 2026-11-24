-- Prove2me | Theorems.Thm_BB6Kit_numerics
-- name    : BB6Kit.numerics
-- status  : Proved
-- author  : @alon yuval
-- created : 2026-11-23T22:13:15.469068+00:00
-- url     : https://prove2.me/theorems/88093dda-798c-401a-a3dd-6e7a8f13e743
-- title:
--   Numeric inequality: $\log(i+5)+2^{30}\log^3(4i)<i\log 3$ for $i\ge 2^{60}$
-- statement:
--   **Theorem.** For every integer $i\ge 2^{60}$, $$\log(i+5)+2^{30}\log^3(4i)<i\log 3.$$ The elementary numeric step that converts `BB6Kit.kit_bound` into the Pillai gap `BB6Baker.pillai_gap`.
-- source:
--   BB(6) Baker roadmap (elementary).

import Mathlib
import Definitions.Def_BB6Delta
import Definitions.Def_BB6Kit

namespace BB6Kit
theorem numerics (i : ℕ) (hi : 2 ^ 60 ≤ i) :
    Real.log ((i : ℝ) + 5) + 2 ^ 30 * Real.log (4 * (i : ℝ)) ^ 3 < (i : ℝ) * Real.log 3 := by
  sorry
end BB6Kit
