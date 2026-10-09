-- Prove2me | Theorems.Thm_ActuarialValuation_finiteMortalityInnovation_after_death
-- name    : ActuarialValuation.finiteMortalityInnovation_after_death
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T07:12:45.322987+00:00
-- url     : https://prove2.me/theorems/62ad77de-f39f-4452-9977-7c2c86062e6b
-- title:
--   Annual innovation vanishes after policy has already ended
-- statement:
--   Neither death in year t nor survival to its start occurs after the individual's death year.
--
--   **Mathematical statement**
--
--   $$
--   K<t\Rightarrow I_t=0
--   $$
-- source:
--   Shiu and Xiong (2021), An elementary derivation of Hattendorff's theorem, European Actuarial Journal 11, 319-323, equations (1)-(3), https://doi.org/10.1007/s13385-020-00256-9; Gerber (1997), Life Insurance Mathematics, 3rd ed., Ch.6 Sec.6.7; Gerber Leung Shiu (2003), Indicator Function and Hattendorff Theorem, https://doi.org/10.1080/10920277.2003.10596075

import Mathlib
import Definitions.Def_actuarial_finiteMortalityInnovation
open MeasureTheory

namespace ActuarialValuation

theorem finiteMortalityInnovation_after_death {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (K : Ω → ℕ) (t : ℕ) (ω : Ω) (hK : K ω < t)
  :
  finiteMortalityInnovation w K t ω = 0 := by sorry

end ActuarialValuation
