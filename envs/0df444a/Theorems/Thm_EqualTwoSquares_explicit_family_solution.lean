-- Prove2me | Theorems.Thm_EqualTwoSquares_explicit_family_solution
-- name    : EqualTwoSquares.explicit_family_solution
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-26T11:24:41.330461+00:00
-- url     : https://prove2.me/theorems/c3353b61-b413-4f77-ac0f-318a0117c88e
-- title:
--   The family gives a positive solution with four pairwise distinct entries
-- statement:
--   Let n be an integer with 4 <= n. Then the quadruple with entries 1, n^2 - n + 1, 2n - 1 and n^2 - n - 1 satisfies 1^2 + (n^2 - n + 1)^2 = (2n - 1)^2 + (n^2 - n - 1)^2, all four entries are strictly positive, and the four entries are pairwise distinct.
-- source:
--   Mission target; machine-checked locally in examples/two-squares/Family.lean.

import Mathlib

namespace EqualTwoSquares

/-- Objective 2 assembled: a positive solution with four pairwise distinct entries. -/
theorem explicit_family_solution {n : ℤ} (hn : 4 ≤ n) :
    (1 : ℤ)^2 + (n^2 - n + 1)^2 = (2 * n - 1)^2 + (n^2 - n - 1)^2 ∧
      (0 < (1 : ℤ) ∧ 0 < n^2 - n + 1 ∧ 0 < 2 * n - 1 ∧ 0 < n^2 - n - 1) ∧
        ((1 : ℤ) ≠ 2 * n - 1 ∧
          (1 : ℤ) ≠ n^2 - n - 1 ∧
            (1 : ℤ) ≠ n^2 - n + 1 ∧
              2 * n - 1 ≠ n^2 - n - 1 ∧
                2 * n - 1 ≠ n^2 - n + 1 ∧
                  n^2 - n - 1 ≠ n^2 - n + 1) := by sorry

end EqualTwoSquares
