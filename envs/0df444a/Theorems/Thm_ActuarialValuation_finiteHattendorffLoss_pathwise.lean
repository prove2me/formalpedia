-- Prove2me | Theorems.Thm_ActuarialValuation_finiteHattendorffLoss_pathwise
-- name    : ActuarialValuation.finiteHattendorffLoss_pathwise
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T16:20:33.558974+00:00
-- url     : https://prove2.me/theorems/d811663a-a7fb-4431-beee-61d9b13a4751
-- title:
--   Insurer loss equals opening reserve plus mortality innovation portfolio
-- statement:
--   The XIX pathwise reserve-loss identity and derived annual probability rates yield an exact scenario-level representation of insurer loss.
--
--   **Mathematical statement**
--
--   $$
--   L_n(\omega)=V_0+\sum_{t<n}\rho_t I_t(\omega)
--   $$
-- source:
--   Original derived finite-horizon actuarial declaration. E. S. W. Shiu and X. Xiong (2021), An elementary derivation of Hattendorff's theorem, European Actuarial Journal 11, printed page 321 (pp. 319–323), Shiu–Xiong (2021), equations (2), (6)–(8), fully discrete Hattendorff variance; https://doi.org/10.1007/s13385-020-00256-9. This individual finite-scenario Lean definition or theorem, including the terminal reserve and finite range, is original derived mathematics rather than a verbatim source theorem. Dependencies: published mortality definitions from Actuarial XVI and published reserve-loss definitions from Actuarial XIX.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_finiteHattendorffLoss
import Definitions.Def_actuarial_finiteHattendorffNetAtRisk
import Definitions.Def_actuarial_finiteMortalityDeathRate
import Definitions.Def_actuarial_finiteMortalityDiscountedShock
import Definitions.Def_actuarial_finiteMortalitySurvivalMass
import Definitions.Def_actuarial_finiteMortalitySurvivalRate
import Definitions.Def_actuarial_finiteReserveAnnualBalance

namespace ActuarialValuation

theorem finiteHattendorffLoss_pathwise {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (K : Ω → ℕ) (n : ℕ) (v : ℝ)
  (premium benefit reserve : ℕ → ℝ)
  (hw : ∀ ω, 0 ≤ w ω) (hsum : (∑ ω : Ω, w ω) = 1)
  (hS : ∀ t ∈ Finset.range n, 0 < finiteMortalitySurvivalMass w K t)
  (hR : ∀ t ∈ Finset.range n,
    finiteReserveAnnualBalance v reserve premium benefit
      (finiteMortalitySurvivalRate w K) (finiteMortalityDeathRate w K) t) (ω : Ω)
  :
  finiteHattendorffLoss K n v premium benefit reserve ω =
  reserve 0 + finiteMortalityDiscountedShock w K
    (finiteHattendorffNetAtRisk v benefit reserve) n ω := by sorry

end ActuarialValuation
