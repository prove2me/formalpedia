-- Prove2me | Theorems.Thm_DiazModulus_s0_add_mem
-- name    : DiazModulus.s0_add_mem
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-10-04T03:30:41.676184+00:00
-- url     : https://prove2.me/theorems/87fc10f6-49c6-4073-8eb8-9a5bebe8ea57
-- title:
--   S₀ closed under addition
-- statement:
--   Let `S₀ = { γ ∈ ℂ : γ algebraic over ℚ and e^{γ/(iπ)} algebraic over ℚ }`.
--   Then `S₀` is closed under addition: if `γ₁, γ₂ ∈ S₀` then `γ₁ + γ₂ ∈ S₀`.

import Mathlib

namespace DiazModulus
theorem s0_add_mem :
    ∀ γ₁ γ₂ : ℂ, IsAlgebraic ℚ γ₁ →
      IsAlgebraic ℚ (Complex.exp (γ₁ / (((Real.pi : ℝ) : ℂ) * Complex.I))) →
      IsAlgebraic ℚ γ₂ →
      IsAlgebraic ℚ (Complex.exp (γ₂ / (((Real.pi : ℝ) : ℂ) * Complex.I))) →
      IsAlgebraic ℚ (γ₁ + γ₂) ∧
        IsAlgebraic ℚ (Complex.exp ((γ₁ + γ₂) / (((Real.pi : ℝ) : ℂ) * Complex.I))) := by sorry
end DiazModulus
