-- Prove2me | Theorems.Thm_FiniteEnergyPlane_monotone_of_add_le_two_mul_of_bddBelow
-- name    : FiniteEnergyPlane.monotone_of_add_le_two_mul_of_bddBelow
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-29T20:48:02.883698+00:00
-- url     : https://prove2.me/theorems/c072736d-bdd2-4d85-b011-750ebe868f2a
-- title:
--   A midpoint-concave real sequence that is bounded below is nondecreasing
-- statement:
--   Let $(a_k)_{k\in\mathbb{N}}$ be a real sequence with $a_k\ge m$ for all $k$, for some $m\in\mathbb{R}$, and with $a_k+a_{k+2}\le 2a_{k+1}$ for all $k$. Then $(a_k)$ is nondecreasing.
--
--   A discrete analogue of the fact that a concave function on $[0,\infty)$ that is bounded below is nondecreasing. It is useful for comparing optimal rates attached to successive orders.
--
--   **Formalization Note** The conclusion is `Monotone a` for `a : ℕ → ℝ`.
-- source:
--   Elementary real analysis; used for U. Hryniewicz, J. Symplectic Geom. 12 (2014), Theorem 2.10

import Mathlib

namespace FiniteEnergyPlane

/-- A real sequence on `ℕ` that is bounded below and satisfies `a k + a (k + 2) ≤ 2 a (k + 1)` for
all `k` is monotone. -/
theorem monotone_of_add_le_two_mul_of_bddBelow (a : ℕ → ℝ) (m : ℝ) (hm : ∀ k, m ≤ a k)
    (hc : ∀ k, a k + a (k + 2) ≤ 2 * a (k + 1)) : Monotone a := by
  sorry

end FiniteEnergyPlane
