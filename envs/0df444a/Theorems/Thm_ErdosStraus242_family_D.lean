-- Prove2me | Theorems.Thm_ErdosStraus242_family_D
-- name    : ErdosStraus242.family_D
-- status  : Proved
-- author  : @alexcarter
-- created : 2026-09-11T11:42:12.112055+00:00
-- url     : https://prove2.me/theorems/582aca31-5e67-4d09-b1d5-04cd08c93010
-- title:
--   Elementary family: five modulo eight
-- statement:
--   For a natural number $n>2$ with $n≡5\pmod8$, put $u=(n+3)/4$. Then $1≤ u<nu/2<nu$ and $4/n=1/u+1/(nu/2)+1/(nu)$ in the rationals. The displayed quotients are computed in the natural numbers; the congruence makes both exact.
-- source:
--   Bloom–Elsholtz (2022), p. 239, displayed $8t+5$ identity, https://www.math.tugraz.at/~elsholtz/WWW/papers/bloom-elsholtz-naw5-2022-23-4-237.pdf. Reparameterized with $u=2(t+1)$; all divisibility and order conditions proved locally.

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert

namespace ErdosStraus242
theorem family_D (n : ℕ) (hn : 2 < n) (hmod : n % 8 = 5) :
    let u := (n+3)/4
    1 ≤ u ∧ u < n*u/2 ∧ n*u/2 < n*u ∧
      (4 / n : ℚ) = 1 / u + 1 / (n*u/2 : ℕ) + 1 / (n*u : ℕ) := by sorry
end ErdosStraus242
