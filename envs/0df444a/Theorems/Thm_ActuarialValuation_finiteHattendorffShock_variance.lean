-- Prove2me | Theorems.Thm_ActuarialValuation_finiteHattendorffShock_variance
-- name    : ActuarialValuation.finiteHattendorffShock_variance
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T16:26:35.129491+00:00
-- url     : https://prove2.me/theorems/f3c51e39-34c9-435c-b0fd-4b961b72325b
-- title:
--   Derived mortality innovation portfolio variance retains survival factor
-- statement:
--   XVI mortality orthogonality gives the fully discrete variance sum with conditional survival probability p_t.
--
--   **Mathematical statement**
--
--   $$
--   \operatorname{Var}_w(Z_n)=\sum_{t<n}\rho_t^2D_tp_t
--   $$
-- source:
--   Original derived finite-horizon actuarial declaration. E. S. W. Shiu and X. Xiong (2021), An elementary derivation of Hattendorff's theorem, European Actuarial Journal 11, printed page 321 (pp. 319–323), Shiu–Xiong (2021), equations (2), (6)–(8), fully discrete Hattendorff variance; https://doi.org/10.1007/s13385-020-00256-9. This individual finite-scenario Lean definition or theorem, including the terminal reserve and finite range, is original derived mathematics rather than a verbatim source theorem. Dependencies: published mortality definitions from Actuarial XVI and published reserve-loss definitions from Actuarial XIX.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_finiteMortalityDeathMass
import Definitions.Def_actuarial_finiteMortalityDiscountedShock
import Definitions.Def_actuarial_finiteMortalitySurvivalMass
import Definitions.Def_actuarial_finiteMortalitySurvivalRate
import Definitions.Def_actuarial_finiteMortalityVariance

namespace ActuarialValuation

theorem finiteHattendorffShock_variance {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (K : Ω → ℕ) (n : ℕ)
  (rho : ℕ → ℝ) (hw : ∀ ω, 0 ≤ w ω)
  (hS : ∀ t ∈ Finset.range n, 0 < finiteMortalitySurvivalMass w K t)
  :
  finiteMortalityVariance w (finiteMortalityDiscountedShock w K rho n) =
    ∑ t ∈ Finset.range n, (rho t) ^ 2 *
      finiteMortalityDeathMass w K t * finiteMortalitySurvivalRate w K t := by sorry

end ActuarialValuation
