-- Prove2me | Theorems.Thm_DiazModulus_real_axis_root_of_unity_implies_pi_sq_rat
-- name    : DiazModulus.real_axis_root_of_unity_implies_pi_sq_rat
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-10-04T03:31:11.097648+00:00
-- url     : https://prove2.me/theorems/5e91442f-993e-4322-b7d1-15648b0b5d6a
-- title:
--   Root-of-unity value on the real axis forces γ ∈ π²ℚ
-- statement:
--   Root-of-unity exclusion, elementary half: if `γ` is real and `e^{γ/(iπ)}`
--   is a root of unity, then `γ ∈ π²·ℚ`. (Combined with the proved in-mission
--   `DiazModulus.pi_sq_transcendental`, this gives: for real algebraic
--   `γ ≠ 0`, `e^{γ/(iπ)}` is not a root of unity — the non-degeneracy step of
--   the real-half NL argument.)

import Mathlib

namespace DiazModulus
theorem real_axis_root_of_unity_implies_pi_sq_rat :
    ∀ γ : ℂ, γ.im = 0 →
      IsOfFinOrder (Complex.exp (γ / (((Real.pi : ℝ) : ℂ) * Complex.I))) →
      ∃ q : ℚ, γ = (((q : ℚ)) : ℂ) * ((((Real.pi ^ 2 : ℝ))) : ℂ) := by sorry
end DiazModulus
