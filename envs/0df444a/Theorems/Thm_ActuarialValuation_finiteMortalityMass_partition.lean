-- Prove2me | Theorems.Thm_ActuarialValuation_finiteMortalityMass_partition
-- name    : ActuarialValuation.finiteMortalityMass_partition
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T07:08:59.989736+00:00
-- url     : https://prove2.me/theorems/d056f818-10c1-4ba4-8f93-58a643b227f2
-- title:
--   Death-year and later-survival partition
-- statement:
--   The in-force event at t splits disjointly into K=t and K≥t+1 without requiring weights to be independent.
--
--   **Mathematical statement**
--
--   $$
--   S_t=D_t+S_{t+1}
--   $$
-- source:
--   Shiu and Xiong (2021), An elementary derivation of Hattendorff's theorem, European Actuarial Journal 11, 319-323, equations (1)-(3), https://doi.org/10.1007/s13385-020-00256-9; Gerber (1997), Life Insurance Mathematics, 3rd ed., Ch.6 Sec.6.7; Gerber Leung Shiu (2003), Indicator Function and Hattendorff Theorem, https://doi.org/10.1080/10920277.2003.10596075

import Mathlib
import Definitions.Def_actuarial_finiteMortalityDeathMass
import Definitions.Def_actuarial_finiteMortalitySurvivalMass
open MeasureTheory

namespace ActuarialValuation

theorem finiteMortalityMass_partition {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (K : Ω → ℕ) (t : ℕ)
  :
  finiteMortalitySurvivalMass w K t = finiteMortalityDeathMass w K t + finiteMortalitySurvivalMass w K (t + 1) := by sorry

end ActuarialValuation
