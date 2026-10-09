-- Prove2me | Theorems.Thm_ActuarialValuation_finiteMortalityDiscountedShock_mean_zero
-- name    : ActuarialValuation.finiteMortalityDiscountedShock_mean_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T07:24:49.850484+00:00
-- url     : https://prove2.me/theorems/2f609b41-11e8-4b0f-afbc-a794ffec1be8
-- title:
--   Discounted mortality shock has zero mean
-- statement:
--   Every annual innovation is centred, so a finite deterministic linear combination also has zero weighted expectation.
--
--   **Mathematical statement**
--
--   $$
--   \mathbb E_w[Z_n]=0
--   $$
-- source:
--   Shiu and Xiong (2021), An elementary derivation of Hattendorff's theorem, European Actuarial Journal 11, 319-323, equations (1)-(3), https://doi.org/10.1007/s13385-020-00256-9; Gerber (1997), Life Insurance Mathematics, 3rd ed., Ch.6 Sec.6.7; Gerber Leung Shiu (2003), Indicator Function and Hattendorff Theorem, https://doi.org/10.1080/10920277.2003.10596075

import Mathlib
import Definitions.Def_actuarial_finiteMortalityDiscountedShock
import Definitions.Def_actuarial_finiteMortalitySurvivalMass
open MeasureTheory

namespace ActuarialValuation

theorem finiteMortalityDiscountedShock_mean_zero {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (K : Ω → ℕ) (ρ : ℕ → ℝ) (n : ℕ)
  (hS : ∀ t ∈ Finset.range n, 0 < finiteMortalitySurvivalMass w K t)
  :
  (∑ ω : Ω, w ω * finiteMortalityDiscountedShock w K ρ n ω) = 0 := by sorry

end ActuarialValuation
