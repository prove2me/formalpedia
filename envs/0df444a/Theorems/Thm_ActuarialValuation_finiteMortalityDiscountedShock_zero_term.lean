-- Prove2me | Theorems.Thm_ActuarialValuation_finiteMortalityDiscountedShock_zero_term
-- name    : ActuarialValuation.finiteMortalityDiscountedShock_zero_term
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T07:24:17.974301+00:00
-- url     : https://prove2.me/theorems/0526a70e-22ff-477a-a244-13b799e5d7b8
-- title:
--   Zero-year mortality-shock portfolio is empty
-- statement:
--   The discounted portfolio sum has no covered years when n=0.
--
--   **Mathematical statement**
--
--   $$
--   Z_0=0
--   $$
-- source:
--   Shiu and Xiong (2021), An elementary derivation of Hattendorff's theorem, European Actuarial Journal 11, 319-323, equations (1)-(3), https://doi.org/10.1007/s13385-020-00256-9; Gerber (1997), Life Insurance Mathematics, 3rd ed., Ch.6 Sec.6.7; Gerber Leung Shiu (2003), Indicator Function and Hattendorff Theorem, https://doi.org/10.1080/10920277.2003.10596075

import Mathlib
import Definitions.Def_actuarial_finiteMortalityDiscountedShock
open MeasureTheory

namespace ActuarialValuation

theorem finiteMortalityDiscountedShock_zero_term {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (K : Ω → ℕ) (ρ : ℕ → ℝ) (ω : Ω)
  :
  finiteMortalityDiscountedShock w K ρ 0 ω = 0 := by sorry

end ActuarialValuation
