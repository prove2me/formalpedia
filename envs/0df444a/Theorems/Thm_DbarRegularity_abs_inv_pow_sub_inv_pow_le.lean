-- Prove2me | Theorems.Thm_DbarRegularity_abs_inv_pow_sub_inv_pow_le
-- name    : DbarRegularity.abs_inv_pow_sub_inv_pow_le
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-12T19:38:18.24799+00:00
-- url     : https://prove2.me/theorems/e5fce63b-7e1f-44ca-a1fc-2507b73250ff
-- title:
--   Difference of inverse d-th powers of nearby positive numbers
-- statement:
--   Let $d\in\mathbb{N}$ and $a,b,c\in\mathbb{R}$ with $a>0$, $2a\le c$ and $|b-c|\le a$. Then
--   $$\bigl|b^{-d}-c^{-d}\bigr|\;\le\;\frac{2\,d\,3^{d-1}\,a}{c^{d+1}} .$$
--
--   **Formalization Note.** Real numbers, natural-number powers; $b^{-d}$ is `(b ^ d)⁻¹` and $3^{d-1}$ uses natural subtraction (for $d=0$ both sides are $0$).
-- source:
--   E. M. Stein, Singular Integrals and Differentiability Properties of Functions, Princeton Mathematical Series 30, Princeton University Press (1970), Chapter II, § 4.2, Theorem 3, p. 39

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Ring.Abs

namespace DbarRegularity

/-- Real-variable estimate: if `0 < a`, `2a ≤ c` and `|b - c| ≤ a`, then
`|b^{-d} - c^{-d}| ≤ 2 d 3^{d-1} a / c^{d+1}`. -/
theorem abs_inv_pow_sub_inv_pow_le (d : ℕ) {a b c : ℝ} (ha : 0 < a) (hc : 2 * a ≤ c)
    (hbc : |b - c| ≤ a) :
    |(b ^ d)⁻¹ - (c ^ d)⁻¹| ≤ 2 * d * 3 ^ (d - 1) * a / c ^ (d + 1) := by sorry

end DbarRegularity
