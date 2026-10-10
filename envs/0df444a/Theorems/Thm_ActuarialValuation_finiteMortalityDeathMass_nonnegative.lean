-- Prove2me | Theorems.Thm_ActuarialValuation_finiteMortalityDeathMass_nonnegative
-- name    : ActuarialValuation.finiteMortalityDeathMass_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T07:08:29.324708+00:00
-- url     : https://prove2.me/theorems/ea8ec091-c69f-4207-9ed4-409dfe700c30
-- title:
--   Death-year mass nonnegative
-- statement:
--   Nonnegative finite weights also give a nonnegative death-event mass.
--
--   **Mathematical statement**
--
--   $$
--   D_t\ge0
--   $$
-- source:
--   Shiu and Xiong (2021), An elementary derivation of Hattendorff's theorem, European Actuarial Journal 11, 319-323, equations (1)-(3), https://doi.org/10.1007/s13385-020-00256-9; Gerber (1997), Life Insurance Mathematics, 3rd ed., Ch.6 Sec.6.7; Gerber Leung Shiu (2003), Indicator Function and Hattendorff Theorem, https://doi.org/10.1080/10920277.2003.10596075

import Mathlib
import Definitions.Def_actuarial_finiteMortalityDeathMass
open MeasureTheory

namespace ActuarialValuation

theorem finiteMortalityDeathMass_nonnegative {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (K : Ω → ℕ) (t : ℕ) (hw : ∀ ω, 0 ≤ w ω)
  :
  0 ≤ finiteMortalityDeathMass w K t := by sorry

end ActuarialValuation
