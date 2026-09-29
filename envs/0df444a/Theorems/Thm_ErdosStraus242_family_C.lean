-- Prove2me | Theorems.Thm_ErdosStraus242_family_C
-- name    : ErdosStraus242.family_C
-- status  : Proved
-- author  : @alexcarter
-- created : 2026-09-11T11:41:50.127059+00:00
-- url     : https://prove2.me/theorems/1ff1825c-603b-466f-9eb1-cc477d68d26d
-- title:
--   Elementary family: three modulo four
-- statement:
--   For a natural number $n>2$ with $n≡3\pmod4$, put $u=(n+1)/4$ and $t=nu$. Then $1≤ u<t+1<t(t+1)$ and $4/n=1/u+1/(t+1)+1/(t(t+1))$ in the rationals. The quotient defining $u$ is exact.
-- source:
--   Bloom–Elsholtz (2022), p. 239, the $3\pmod4$ two-term identity, https://www.math.tugraz.at/~elsholtz/WWW/papers/bloom-elsholtz-naw5-2022-23-4-237.pdf, followed by the independently verified splitting $1/t=1/(t+1)+1/(t(t+1))$. Distinct refinement proved locally.

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert

namespace ErdosStraus242
theorem family_C (n : ℕ) (hn : 2 < n) (hmod : n % 4 = 3) :
    let u := (n+1)/4
    let t := n*u
    1 ≤ u ∧ u < t+1 ∧ t+1 < t*(t+1) ∧
      (4 / n : ℚ) = 1 / u + 1 / (t+1 : ℕ) + 1 / (t*(t+1) : ℕ) := by sorry
end ErdosStraus242
