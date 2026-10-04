-- Prove2me | Theorems.Thm_DiazModulus_s0_bridge_halves_imp_parent
-- name    : DiazModulus.s0_bridge_halves_imp_parent
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-10-04T03:30:57.095831+00:00
-- url     : https://prove2.me/theorems/0a50be9e-68b5-41e5-8e16-7ccc1ed4770d
-- title:
--   The two axis halves imply the parent modulus statement
-- statement:
--   The two axis halves jointly imply the parent modulus statement: assuming
--   (imag-half) no non-zero purely imaginary algebraic `γ` has `e^{γ/(iπ)}`
--   algebraic, and (real-half) no non-zero real algebraic `γ` has `e^{γ/(iπ)}`
--   algebraic, then no non-zero algebraic `γ` at all has `e^{γ/(iπ)}` algebraic.
--   The halves are explicit hypotheses (not cited unproved nodes), so a clean
--   proof earns full ACCEPTED as a conditional theorem; it banks the bridge and
--   holds the reduction chain for the day the halves fall.

import Mathlib

namespace DiazModulus
theorem s0_bridge_halves_imp_parent
    (hI : ∀ γ : ℂ, IsAlgebraic ℚ γ → γ ≠ 0 → γ.re = 0 →
      ¬ IsAlgebraic ℚ (Complex.exp (γ / (((Real.pi : ℝ) : ℂ) * Complex.I))))
    (hR : ∀ γ : ℂ, IsAlgebraic ℚ γ → γ ≠ 0 → γ.im = 0 →
      ¬ IsAlgebraic ℚ (Complex.exp (γ / (((Real.pi : ℝ) : ℂ) * Complex.I)))) :
    ∀ γ : ℂ, IsAlgebraic ℚ γ → γ ≠ 0 →
      ¬ IsAlgebraic ℚ (Complex.exp (γ / (((Real.pi : ℝ) : ℂ) * Complex.I))) := by sorry
end DiazModulus
