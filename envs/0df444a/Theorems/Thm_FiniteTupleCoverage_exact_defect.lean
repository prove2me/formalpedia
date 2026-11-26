-- Prove2me | Theorems.Thm_FiniteTupleCoverage_exact_defect
-- name    : FiniteTupleCoverage.exact_defect
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T20:40:24.011618+00:00
-- url     : https://prove2.me/theorems/dee26e7d-eccd-472e-a9b8-d548c78a866a
-- title:
--   Exact coverage from the count of admissible listed tuples
-- statement:
--   Each of finitely many coordinates has its own finite set of admissible symbols. A finite set lists candidate tuples. Count the listed tuples that use only admissible symbols. The number of admissible tuples absent from the list is the product of the coordinate set sizes minus that count. In particular, the count equals the product exactly when the list contains every admissible tuple. The ambient symbol types may be infinite.
-- source:
--   The finite Cartesian product rule and the finite-set identity that partitions a set into its intersection and difference.

import Mathlib

theorem FiniteTupleCoverage.exact_defect {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Type*} [∀ i, DecidableEq (A i)] (allowed : ∀ i, Finset (A i))
    (listed : Finset (∀ i, A i)) :
    let seen := listed.filter (fun r => ∀ i, r i ∈ allowed i)
    ((Fintype.piFinset allowed) \ listed).card = (∏ i, (allowed i).card) - seen.card ∧
    (seen.card = (∏ i, (allowed i).card) ↔ ∀ r, (∀ i, r i ∈ allowed i) → r ∈ listed) := by sorry
