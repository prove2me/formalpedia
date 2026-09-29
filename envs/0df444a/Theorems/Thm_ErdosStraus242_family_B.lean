-- Prove2me | Theorems.Thm_ErdosStraus242_family_B
-- name    : ErdosStraus242.family_B
-- status  : Proved
-- author  : @alexcarter
-- created : 2026-09-11T11:41:40.912195+00:00
-- url     : https://prove2.me/theorems/c1d65c9b-327e-4abe-9060-920ca5a039d4
-- title:
--   Elementary family: two modulo three
-- statement:
--   For a natural number $n>2$ with $n≡2\pmod3$, put $u=(n+1)/3$. Then $1≤ u<n<nu$ and $4/n=1/u+1/n+1/(nu)$ in the rationals. The quotient defining $u$ is exact.
-- source:
--   Elementary identity independently derived and locally verified for https://www.erdosproblems.com/242; use $3u=n+1$. Not attributed as a verbatim theorem to a secondary summary.

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert

namespace ErdosStraus242
theorem family_B (n : ℕ) (hn : 2 < n) (hmod : n % 3 = 2) :
    let u := (n+1)/3
    1 ≤ u ∧ u < n ∧ n < n*u ∧
      (4 / n : ℚ) = 1 / u + 1 / n + 1 / (n*u : ℕ) := by sorry
end ErdosStraus242
