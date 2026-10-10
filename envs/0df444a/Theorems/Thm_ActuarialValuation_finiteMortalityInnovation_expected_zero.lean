-- Prove2me | Theorems.Thm_ActuarialValuation_finiteMortalityInnovation_expected_zero
-- name    : ActuarialValuation.finiteMortalityInnovation_expected_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T07:13:57.191139+00:00
-- url     : https://prove2.me/theorems/09844d47-656e-48b8-ac56-c490a83d3a89
-- title:
--   Finite mortality innovation has zero weighted mean
-- statement:
--   Subtracting q_t times the probability of being in force centres the death-year indicator.
--
--   **Mathematical statement**
--
--   $$
--   \mathbb E_w[I_t]=D_t-q_tS_t=0
--   $$
-- source:
--   Shiu and Xiong (2021), An elementary derivation of Hattendorff's theorem, European Actuarial Journal 11, 319-323, equations (1)-(3), https://doi.org/10.1007/s13385-020-00256-9; Gerber (1997), Life Insurance Mathematics, 3rd ed., Ch.6 Sec.6.7; Gerber Leung Shiu (2003), Indicator Function and Hattendorff Theorem, https://doi.org/10.1080/10920277.2003.10596075

import Mathlib
import Definitions.Def_actuarial_finiteMortalityInnovation
import Definitions.Def_actuarial_finiteMortalitySurvivalMass
open MeasureTheory

namespace ActuarialValuation

theorem finiteMortalityInnovation_expected_zero {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (K : Ω → ℕ) (t : ℕ) (hS : 0 < finiteMortalitySurvivalMass w K t)
  :
  (∑ ω : Ω, w ω * finiteMortalityInnovation w K t ω) = 0 := by sorry

end ActuarialValuation
