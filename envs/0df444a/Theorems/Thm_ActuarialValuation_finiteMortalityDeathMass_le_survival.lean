-- Prove2me | Theorems.Thm_ActuarialValuation_finiteMortalityDeathMass_le_survival
-- name    : ActuarialValuation.finiteMortalityDeathMass_le_survival
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T07:11:14.431705+00:00
-- url     : https://prove2.me/theorems/de05e468-3983-4fe8-a016-f038851d310a
-- title:
--   Death mass bounded by survival mass
-- statement:
--   Every scenario with K=t was in force at time t, giving the corresponding weighted event inclusion.
--
--   **Mathematical statement**
--
--   $$
--   D_t\le S_t
--   $$
-- source:
--   Shiu and Xiong (2021), An elementary derivation of Hattendorff's theorem, European Actuarial Journal 11, 319-323, equations (1)-(3), https://doi.org/10.1007/s13385-020-00256-9; Gerber (1997), Life Insurance Mathematics, 3rd ed., Ch.6 Sec.6.7; Gerber Leung Shiu (2003), Indicator Function and Hattendorff Theorem, https://doi.org/10.1080/10920277.2003.10596075

import Mathlib
import Definitions.Def_actuarial_finiteMortalityDeathMass
import Definitions.Def_actuarial_finiteMortalitySurvivalMass
open MeasureTheory

namespace ActuarialValuation

theorem finiteMortalityDeathMass_le_survival {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (K : Ω → ℕ) (t : ℕ) (hw : ∀ ω, 0 ≤ w ω)
  :
  finiteMortalityDeathMass w K t ≤ finiteMortalitySurvivalMass w K t := by sorry

end ActuarialValuation
