-- Prove2me | Theorems.Thm_ActuarialValuation_finiteHattendorffShock_expected_zero
-- name    : ActuarialValuation.finiteHattendorffShock_expected_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T16:20:55.253612+00:00
-- url     : https://prove2.me/theorems/e9a5c05e-69d9-4458-a7f3-2e1565cd2a63
-- title:
--   Discounted mortality shock has zero expected value
-- statement:
--   Since each properly defined annual death surprise has zero weighted mean, their deterministic finite linear combination is centred.
--
--   **Mathematical statement**
--
--   $$
--   \mathbb E_w[Z_n]=0
--   $$
-- source:
--   Original derived finite-horizon actuarial declaration. E. S. W. Shiu and X. Xiong (2021), An elementary derivation of Hattendorff's theorem, European Actuarial Journal 11, printed page 320 (pp. 319–323), Shiu–Xiong (2021), equations (1)–(5), fully discrete loss and prospective-reserve recursion; https://doi.org/10.1007/s13385-020-00256-9. This individual finite-scenario Lean definition or theorem, including the terminal reserve and finite range, is original derived mathematics rather than a verbatim source theorem. Dependencies: published mortality definitions from Actuarial XVI and published reserve-loss definitions from Actuarial XIX.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_finiteMortalityDiscountedShock
import Definitions.Def_actuarial_finiteMortalitySurvivalMass

namespace ActuarialValuation

theorem finiteHattendorffShock_expected_zero {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (K : Ω → ℕ) (n : ℕ)
  (rho : ℕ → ℝ)
  (hS : ∀ t ∈ Finset.range n, 0 < finiteMortalitySurvivalMass w K t)
  :
  (∑ ω : Ω, w ω * finiteMortalityDiscountedShock w K rho n ω) = 0 := by sorry

end ActuarialValuation
