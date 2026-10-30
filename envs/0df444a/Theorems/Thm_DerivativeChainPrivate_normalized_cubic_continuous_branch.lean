-- Prove2me | Theorems.Thm_DerivativeChainPrivate_normalized_cubic_continuous_branch
-- name    : DerivativeChainPrivate.normalized_cubic_continuous_branch
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T20:14:52.270959+00:00
-- url     : https://prove2.me/theorems/34baa95a-4c4f-43be-aef7-dc030d5d416f
-- title:
--   Continuous nonsingular root branch of the normalized cubic
-- statement:
--   On the closed first quadrant of complex parameters beta, there is a continuous root f(beta) of f^3-f=beta with real part at least one, nonnegative imaginary part, real_part(f)^2 >= 1+3 imaginary_part(f)^2, and nonzero derivative 3 f^2-1. This is a root-branch theorem for the normalized cubic, not an unrestricted derivative-chain bound.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/cube_continuation/Source/CubicBranch.lean#L35-L74

import Mathlib
namespace DerivativeChainPrivate
end DerivativeChainPrivate
open DerivativeChainPrivate Filter Topology Polynomial
open scoped BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

theorem DerivativeChainPrivate.normalized_cubic_continuous_branch :
    ∃ f : {β : ℂ // 0 ≤ β.re ∧ 0 ≤ β.im} → ℂ,
      Continuous f ∧ ∀ β,
        f β ^ 3 - f β = β.val ∧ 1 ≤ (f β).re ∧ 0 ≤ (f β).im ∧
        1 + 3 * (f β).im ^ 2 ≤ (f β).re ^ 2 ∧ 3 * f β ^ 2 - 1 ≠ 0 := by sorry
