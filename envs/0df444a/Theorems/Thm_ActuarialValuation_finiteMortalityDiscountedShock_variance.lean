-- Prove2me | Theorems.Thm_ActuarialValuation_finiteMortalityDiscountedShock_variance
-- name    : ActuarialValuation.finiteMortalityDiscountedShock_variance
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T07:26:46.514082+00:00
-- url     : https://prove2.me/theorems/8a6f65dc-20a9-402b-8767-c170d81a5769
-- title:
--   Fully discrete Hattendorff-style innovation variance allocation
-- statement:
--   Using *derived*, not assumed, cross-year orthogonality, the variance of annual mortality shocks is the sum of their net-amount-at-risk squares times death mass and conditional survival rate.
--
--   **Mathematical statement**
--
--   $$
--   \operatorname{Var}_w(Z_n)=\sum_{t<n}\rho_t^2D_tp_t
--   $$
-- source:
--   Shiu and Xiong (2021), An elementary derivation of Hattendorff's theorem, European Actuarial Journal 11, 319-323, equations (1)-(3), https://doi.org/10.1007/s13385-020-00256-9; Gerber (1997), Life Insurance Mathematics, 3rd ed., Ch.6 Sec.6.7; Gerber Leung Shiu (2003), Indicator Function and Hattendorff Theorem, https://doi.org/10.1080/10920277.2003.10596075

import Mathlib
import Definitions.Def_actuarial_finiteMortalityDeathMass
import Definitions.Def_actuarial_finiteMortalityDiscountedShock
import Definitions.Def_actuarial_finiteMortalitySurvivalMass
import Definitions.Def_actuarial_finiteMortalitySurvivalRate
import Definitions.Def_actuarial_finiteMortalityVariance
open MeasureTheory

namespace ActuarialValuation

theorem finiteMortalityDiscountedShock_variance {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (K : Ω → ℕ) (ρ : ℕ → ℝ) (n : ℕ) (hw : ∀ ω, 0 ≤ w ω)
  (hS : ∀ t ∈ Finset.range n, 0 < finiteMortalitySurvivalMass w K t)
  :
  finiteMortalityVariance w (finiteMortalityDiscountedShock w K ρ n) =
    ∑ t ∈ Finset.range n, (ρ t) ^ 2 *
      finiteMortalityDeathMass w K t * finiteMortalitySurvivalRate w K t := by sorry

end ActuarialValuation
