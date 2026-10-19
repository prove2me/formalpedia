-- Prove2me | Theorems.Thm_DynSetValue_DPP_equation_3_4
-- name    : DynSetValue.DPP.equation_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:21:29.526575+00:00
-- url     : https://prove2.me/theorems/ecfb0645-4f84-4f24-a84a-cf8734fa476c
-- title:
--   Equation (3.4) — cost continuity in time and path
-- statement:
--   Under Assumptions 3.1 and 3.6(i), there is one modulus of continuity $\rho$ for all admissible controls and all histories such that
--
--   $$
--   \|J(t,\omega,\alpha)-J(\widetilde t,\widetilde\omega,\alpha)\|
--   \le\rho\!\left(\mathbf d((t,\omega),(\widetilde t,\widetilde\omega))\right).
--   $$
--
--   The norm on cost vectors is Euclidean. The same modulus across profiles is what lets approximate equilibria be compared at nearby histories.
-- source:
--   Feinstein, Rudloff, Zhang, Dynamic set values for nonzero sum games with multiple equilibriums, arXiv:2002.00449v2, p. 24, equation (3.4), proof of Theorem 3.7(i)

import Mathlib
import Definitions.Def_DynSetValue_DPP_SetValue

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace DynSetValue.DPP

/-- Equation (3.4), p. 24. -/
theorem equation_3_4 {T : ℝ} (hT : 0 < T) {d N : ℕ}
    (G : Game T hT d N) (P0 : Measure (Ω T d))
    (hP0 : IsWiener hT P0) (h31 : Assumption31 G P0)
    (h36i : Assumption36i G) :
    ∃ ρ : ℝ → ℝ, IsModulus ρ ∧
      ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ t' ∈ Set.Icc (0 : ℝ) T,
        ∀ ω ω' (α : Profile hT G), IsProfile hT G P0 α →
          ‖J hT G P0 t ω α - J hT G P0 t' ω' α‖ ≤
            ρ (distD hT t ω t' ω') := by sorry

end DynSetValue.DPP
