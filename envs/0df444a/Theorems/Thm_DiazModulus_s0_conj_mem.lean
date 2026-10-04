-- Prove2me | Theorems.Thm_DiazModulus_s0_conj_mem
-- name    : DiazModulus.s0_conj_mem
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-10-04T03:30:53.021983+00:00
-- url     : https://prove2.me/theorems/1afabb12-d7d5-4693-ad02-527b0a1fec34
-- title:
--   S₀ closed under conjugation
-- statement:
--   `S₀` is closed under complex conjugation: if `γ ∈ S₀` then `γ̄ ∈ S₀`.

import Mathlib

namespace DiazModulus
theorem s0_conj_mem :
    ∀ γ : ℂ, IsAlgebraic ℚ γ →
      IsAlgebraic ℚ (Complex.exp (γ / (((Real.pi : ℝ) : ℂ) * Complex.I))) →
      IsAlgebraic ℚ (starRingEnd ℂ γ) ∧
        IsAlgebraic ℚ (Complex.exp ((starRingEnd ℂ γ) / (((Real.pi : ℝ) : ℂ) * Complex.I))) := by sorry
end DiazModulus
