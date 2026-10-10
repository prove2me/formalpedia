-- Prove2me | Theorems.Thm_ActuarialValuation_finiteHattendorffReserveLoss_fundamental
-- name    : ActuarialValuation.finiteHattendorffReserveLoss_fundamental
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T16:40:09.134977+00:00
-- url     : https://prove2.me/theorems/2805c55c-794b-4aab-be20-d30d6402dfda
-- title:
--   Fully discrete finite-horizon reserve-loss Hattendorff theorem
-- statement:
--   Under a finite lifetime probability law and consistent prospective reserve recurrence, expected finite-horizon insurer loss is the opening reserve and its variance is the sum over years of squared discounted net amounts at risk multiplied by death probability and the conditional survival factor.
--
--   **Mathematical statement**
--
--   $$
--   \mathbb E_w[L_n]=V_0,\quad \operatorname{Var}_w(L_n)=\sum_{t<n}\rho_t^2D_tp_t
--   $$
-- source:
--   Original derived finite-horizon actuarial declaration. E. S. W. Shiu and X. Xiong (2021), An elementary derivation of Hattendorff's theorem, European Actuarial Journal 11, printed page 321 (pp. 319–323), Shiu–Xiong (2021), equations (2), (6)–(8), fully discrete Hattendorff variance; https://doi.org/10.1007/s13385-020-00256-9. This individual finite-scenario Lean definition or theorem, including the terminal reserve and finite range, is original derived mathematics rather than a verbatim source theorem. Dependencies: published mortality definitions from Actuarial XVI and published reserve-loss definitions from Actuarial XIX.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_finiteHattendorffExpectedLoss
import Definitions.Def_actuarial_finiteHattendorffLossVariance
import Definitions.Def_actuarial_finiteHattendorffNetAtRisk
import Definitions.Def_actuarial_finiteMortalityDeathMass
import Definitions.Def_actuarial_finiteMortalityDeathRate
import Definitions.Def_actuarial_finiteMortalitySurvivalMass
import Definitions.Def_actuarial_finiteMortalitySurvivalRate
import Definitions.Def_actuarial_finiteReserveAnnualBalance

namespace ActuarialValuation

theorem finiteHattendorffReserveLoss_fundamental {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (K : Ω → ℕ) (n : ℕ) (v : ℝ)
  (premium benefit reserve : ℕ → ℝ)
  (hw : ∀ ω, 0 ≤ w ω) (hsum : (∑ ω : Ω, w ω) = 1)
  (hS : ∀ t ∈ Finset.range n, 0 < finiteMortalitySurvivalMass w K t)
  (hR : ∀ t ∈ Finset.range n,
    finiteReserveAnnualBalance v reserve premium benefit
      (finiteMortalitySurvivalRate w K) (finiteMortalityDeathRate w K) t)
  :
  (finiteHattendorffExpectedLoss w K n v premium benefit reserve = reserve 0)
  ∧ (finiteHattendorffLossVariance w K n v premium benefit reserve =
    ∑ t ∈ Finset.range n,
      (finiteHattendorffNetAtRisk v benefit reserve t) ^ 2 *
      finiteMortalityDeathMass w K t * finiteMortalitySurvivalRate w K t) := by sorry

end ActuarialValuation
