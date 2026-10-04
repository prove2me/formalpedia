-- Prove2me | Theorems.Thm_DiazModulus_s0_rat_scale_mem
-- name    : DiazModulus.s0_rat_scale_mem
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-10-04T03:30:39.298706+00:00
-- url     : https://prove2.me/theorems/8c112536-9104-4ca8-abd7-c618b45eb9af
-- title:
--   S₀ closed under rational scaling
-- statement:
--   `S₀` is closed under rational scaling: if `γ ∈ S₀` and `q ∈ ℚ`, then
--   `q·γ ∈ S₀`.

import Mathlib

namespace DiazModulus
theorem s0_rat_scale_mem :
    ∀ (q : ℚ) (γ : ℂ), IsAlgebraic ℚ γ →
      IsAlgebraic ℚ (Complex.exp (γ / (((Real.pi : ℝ) : ℂ) * Complex.I))) →
      IsAlgebraic ℚ (((q : ℚ) : ℂ) * γ) ∧
        IsAlgebraic ℚ (Complex.exp ((((q : ℚ) : ℂ) * γ) / (((Real.pi : ℝ) : ℂ) * Complex.I))) := by sorry
end DiazModulus
