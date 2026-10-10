-- Prove2me | Theorems.Thm_ActuarialValuation_finiteMortalityRates_sum
-- name    : ActuarialValuation.finiteMortalityRates_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T07:11:47.397992+00:00
-- url     : https://prove2.me/theorems/7c14e7ef-f0d2-4100-8cd6-ce75a9c1e2ab
-- title:
--   Conditional death and survival rates sum to one
-- statement:
--   The finite death/survival partition gives conditional q_t+p_t=1 at positive in-force mass.
--
--   **Mathematical statement**
--
--   $$
--   q_t+p_t=1
--   $$
-- source:
--   Shiu and Xiong (2021), An elementary derivation of Hattendorff's theorem, European Actuarial Journal 11, 319-323, equations (1)-(3), https://doi.org/10.1007/s13385-020-00256-9; Gerber (1997), Life Insurance Mathematics, 3rd ed., Ch.6 Sec.6.7; Gerber Leung Shiu (2003), Indicator Function and Hattendorff Theorem, https://doi.org/10.1080/10920277.2003.10596075

import Mathlib
import Definitions.Def_actuarial_finiteMortalityDeathRate
import Definitions.Def_actuarial_finiteMortalitySurvivalMass
import Definitions.Def_actuarial_finiteMortalitySurvivalRate
open MeasureTheory

namespace ActuarialValuation

theorem finiteMortalityRates_sum {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (K : Ω → ℕ) (t : ℕ) (hS : 0 < finiteMortalitySurvivalMass w K t)
  :
  finiteMortalityDeathRate w K t + finiteMortalitySurvivalRate w K t = 1 := by sorry

end ActuarialValuation
