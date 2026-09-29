-- Prove2me | Theorems.Thm_ErdosStraus242_clear_denominators
-- name    : ErdosStraus242.clear_denominators
-- status  : Proved
-- author  : @alexcarter
-- created : 2026-09-11T11:40:50.745115+00:00
-- url     : https://prove2.me/theorems/ac499935-caa6-4441-b159-1e1011511f5d
-- title:
--   Denominator clearing over the integers
-- statement:
--   For positive natural numbers $n,x,y,z$, the rational identity $4/n=1/x+1/y+1/z$ holds if and only if the integer identity $4xyz=n(yz+xz+xy)$ holds. No order or distinctness assumption is required for this algebraic equivalence.
-- source:
--   Independent denominator-clearing derivation from the equation in Erdős Problem 242, https://www.erdosproblems.com/242; locally proved over the exact target environment.

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert

namespace ErdosStraus242
theorem clear_denominators (n x y z : ℕ)
    (hn : 0 < n) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    ((4 / n : ℚ) = 1 / x + 1 / y + 1 / z) ↔
    (4 * (x : ℤ) * y * z = (n : ℤ) * (y * z + x * z + x * y)) := by sorry
end ErdosStraus242
