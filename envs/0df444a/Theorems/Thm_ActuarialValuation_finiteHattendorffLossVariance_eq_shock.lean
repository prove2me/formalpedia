-- Prove2me | Theorems.Thm_ActuarialValuation_finiteHattendorffLossVariance_eq_shock
-- name    : ActuarialValuation.finiteHattendorffLossVariance_eq_shock
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T16:23:54.51206+00:00
-- url     : https://prove2.me/theorems/daa48b19-5350-4ab0-addc-29b2e240464b
-- title:
--   Insurer-loss variance is the mortality innovation variance
-- statement:
--   Use the pathwise reserve-loss identity and cash-shift variance invariance to remove the deterministic opening reserve from the loss variance.
--
--   **Mathematical statement**
--
--   $$
--   \operatorname{Var}_w(L_n)=\operatorname{Var}_w(Z_n)
--   $$
-- source:
--   Original derived finite-horizon actuarial declaration. E. S. W. Shiu and X. Xiong (2021), An elementary derivation of Hattendorff's theorem, European Actuarial Journal 11, printed page 321 (pp. 319–323), Shiu–Xiong (2021), equations (2), (6)–(8), fully discrete Hattendorff variance; https://doi.org/10.1007/s13385-020-00256-9. This individual finite-scenario Lean definition or theorem, including the terminal reserve and finite range, is original derived mathematics rather than a verbatim source theorem. Dependencies: published mortality definitions from Actuarial XVI and published reserve-loss definitions from Actuarial XIX.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_finiteHattendorffLossVariance
import Definitions.Def_actuarial_finiteHattendorffNetAtRisk
import Definitions.Def_actuarial_finiteMortalityDeathRate
import Definitions.Def_actuarial_finiteMortalityDiscountedShock
import Definitions.Def_actuarial_finiteMortalitySurvivalMass
import Definitions.Def_actuarial_finiteMortalitySurvivalRate
import Definitions.Def_actuarial_finiteMortalityVariance
import Definitions.Def_actuarial_finiteReserveAnnualBalance

namespace ActuarialValuation

theorem finiteHattendorffLossVariance_eq_shock {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (K : Ω → ℕ) (n : ℕ) (v : ℝ)
  (premium benefit reserve : ℕ → ℝ)
  (hw : ∀ ω, 0 ≤ w ω) (hsum : (∑ ω : Ω, w ω) = 1)
  (hS : ∀ t ∈ Finset.range n, 0 < finiteMortalitySurvivalMass w K t)
  (hR : ∀ t ∈ Finset.range n,
    finiteReserveAnnualBalance v reserve premium benefit
      (finiteMortalitySurvivalRate w K) (finiteMortalityDeathRate w K) t)
  :
  finiteHattendorffLossVariance w K n v premium benefit reserve =
  finiteMortalityVariance w (finiteMortalityDiscountedShock w K
    (finiteHattendorffNetAtRisk v benefit reserve) n) := by sorry

end ActuarialValuation
