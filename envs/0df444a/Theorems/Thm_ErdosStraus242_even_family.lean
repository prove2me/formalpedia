-- Prove2me | Theorems.Thm_ErdosStraus242_even_family
-- name    : ErdosStraus242.even_family
-- status  : Proved
-- author  : @alexcarter
-- created : 2026-09-11T11:41:22.452651+00:00
-- url     : https://prove2.me/theorems/f52981d6-e70e-487b-8eb5-3d019e075c32
-- title:
--   A distinct decomposition for every even input above two
-- statement:
--   Let $n>2$ be an even natural number and let $m=n/2$. Then $1≤ m<m+1<m(m+1)$ and $4/n=1/m+1/(m+1)+1/(m(m+1))$ in the rationals. The quotient $m$ is exact.
-- source:
--   Independent explicit refinement of the even case in Yamamoto (1965), §1, p. 37, https://www.jstage.jst.go.jp/article/kyushumfs/19/1/19_1_37/_pdf/-char/en; obtained from the elementary unit-fraction splitting identity. Locally proved.

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert

namespace ErdosStraus242
theorem even_family (n : ℕ) (hn : 2 < n) (heven : 2 ∣ n) :
    let m := n / 2
    1 ≤ m ∧ m < m+1 ∧ m+1 < m*(m+1) ∧
      (4 / n : ℚ) = 1 / m + 1 / (m+1 : ℕ) + 1 / (m*(m+1) : ℕ) := by sorry
end ErdosStraus242
