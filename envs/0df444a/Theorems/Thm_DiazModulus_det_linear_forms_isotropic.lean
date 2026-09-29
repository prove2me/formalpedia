-- Prove2me | Theorems.Thm_DiazModulus_det_linear_forms_isotropic
-- name    : DiazModulus.det_linear_forms_isotropic
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T04:56:42.185327+00:00
-- url     : https://prove2.me/theorems/0b3c72ec-8228-4f25-98b1-3849adb9ba9f
-- title:
--   The determinant of a 2×2 matrix of rational linear forms in three variables has a non-trivial rational zero
-- statement:
--   **Determinantal ternary forms are isotropic.**
--
--   Let $L = (L_{ij})$ be a $2\times2$ matrix of linear forms in three variables with rational coefficients. Then the quadratic form $\det L$ has a non-trivial rational zero: some $v \in \mathbb{Q}^{3}$, $v \neq 0$, satisfies $L_{00}(v)L_{11}(v) = L_{01}(v)L_{10}(v)$. Take $v$ in the common kernel of $L_{00}$ and $L_{01}$.
--
--   Consequently a rational ternary quadratic form without non-trivial rational zeros, such as $\tfrac12(X_1^{2} + X_2^{2}) + X_3^{2}$, is never the determinant of such a matrix.
--
--   **Novelty.** None claimed. Classical and elementary.
-- source:
--   Used in the proof of Proposition 5.7(b) of Carlo Perassi, companion note to https://github.com/carlok/diaz-modulus-lean, version 1.9, 25 September 2026 (GitHub release note-v1.9). Formal proof: Diaz modulus mission, 24 September 2026 (C. Perassi). Background: classical; a ternary quadratic form is such a determinant exactly when it is isotropic.

import Mathlib

namespace DiazModulus

theorem det_linear_forms_isotropic (A : Fin 2 → Fin 2 → Fin 3 → ℚ) :
    ∃ v : Fin 3 → ℚ, v ≠ 0 ∧
      (∑ k, A 0 0 k * v k) * (∑ k, A 1 1 k * v k)
        = (∑ k, A 0 1 k * v k) * (∑ k, A 1 0 k * v k) := by sorry

end DiazModulus
