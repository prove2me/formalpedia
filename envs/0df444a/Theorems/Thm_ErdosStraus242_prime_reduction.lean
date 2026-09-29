-- Prove2me | Theorems.Thm_ErdosStraus242_prime_reduction
-- name    : ErdosStraus242.prime_reduction
-- status  : Proved
-- author  : @alexcarter
-- created : 2026-09-11T11:42:30.947361+00:00
-- url     : https://prove2.me/theorems/02ec88cc-8e2d-44f0-8adf-5a71c920c004
-- title:
--   Reduction to primes strictly above two
-- statement:
--   The universal distinct-denominator assertion for all natural numbers $n>2$ is equivalent to the same assertion for all primes $p>2$. The prime $2$ is excluded from the right-hand side; the explicit even family handles all even inputs on the left.
-- source:
--   Erdős Problem 242, https://www.erdosproblems.com/242, prime reduction; Yamamoto (1965), §1 p. 37, https://www.jstage.jst.go.jp/article/kyushumfs/19/1/19_1_37/_pdf/-char/en. Exact distinctness/range adaptation proved locally using the even family and scaling.

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert

namespace ErdosStraus242
theorem prime_reduction :
    (∀ n : ℕ, 2 < n → IsErdosStraus n) ↔
    (∀ p : ℕ, Nat.Prime p → 2 < p → IsErdosStraus p) := by sorry
end ErdosStraus242
