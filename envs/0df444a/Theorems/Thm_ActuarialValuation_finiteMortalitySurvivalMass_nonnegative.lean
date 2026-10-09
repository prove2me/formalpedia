-- Prove2me | Theorems.Thm_ActuarialValuation_finiteMortalitySurvivalMass_nonnegative
-- name    : ActuarialValuation.finiteMortalitySurvivalMass_nonnegative
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T07:07:42.057979+00:00
-- url     : https://prove2.me/theorems/2d296f7f-f21c-4a40-b486-24ea2562887e
-- title:
--   Survival mass nonnegative
-- statement:
--   Nonnegative finite probability weights sum to a nonnegative survival mass.
--
--   **Mathematical statement**
--
--   $$
--   S_t\ge0
--   $$
-- source:
--   Shiu and Xiong (2021), An elementary derivation of Hattendorff's theorem, European Actuarial Journal 11, 319-323, equations (1)-(3), https://doi.org/10.1007/s13385-020-00256-9; Gerber (1997), Life Insurance Mathematics, 3rd ed., Ch.6 Sec.6.7; Gerber Leung Shiu (2003), Indicator Function and Hattendorff Theorem, https://doi.org/10.1080/10920277.2003.10596075

import Mathlib
import Definitions.Def_actuarial_finiteMortalitySurvivalMass
open MeasureTheory

namespace ActuarialValuation

theorem finiteMortalitySurvivalMass_nonnegative {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (K : Ω → ℕ) (t : ℕ) (hw : ∀ ω, 0 ≤ w ω)
  :
  0 ≤ finiteMortalitySurvivalMass w K t := by sorry

end ActuarialValuation
