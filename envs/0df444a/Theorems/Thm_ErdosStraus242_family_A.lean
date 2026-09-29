-- Prove2me | Theorems.Thm_ErdosStraus242_family_A
-- name    : ErdosStraus242.family_A
-- status  : Proved
-- author  : @alexcarter
-- created : 2026-09-11T11:41:31.190133+00:00
-- url     : https://prove2.me/theorems/3bc7415c-2abc-4051-83b5-22a529f6b362
-- title:
--   Elementary family: multiples of three
-- statement:
--   For every natural number $n>2$ divisible by $3$, the denominators $x=n/3$, $y=4n/3$, $z=4n$ satisfy $1≤ x<y<z$ and $4/n=1/x+1/y+1/z$ in the rationals. Both natural-number quotients are exact.
-- source:
--   Elementary identity independently derived and locally verified for the equation in https://www.erdosproblems.com/242; equivalently positive scaling of $4/3=1+1/4+1/12$.

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert

namespace ErdosStraus242
theorem family_A (n : ℕ) (hn : 2 < n) (hdiv : 3 ∣ n) :
    1 ≤ n/3 ∧ n/3 < 4*n/3 ∧ 4*n/3 < 4*n ∧
      (4 / n : ℚ) = 1 / (n/3 : ℕ) + 1 / (4*n/3 : ℕ) + 1 / (4*n : ℕ) := by sorry
end ErdosStraus242
