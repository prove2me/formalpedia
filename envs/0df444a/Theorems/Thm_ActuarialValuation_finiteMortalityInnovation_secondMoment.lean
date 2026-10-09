-- Prove2me | Theorems.Thm_ActuarialValuation_finiteMortalityInnovation_secondMoment
-- name    : ActuarialValuation.finiteMortalityInnovation_secondMoment
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T07:23:23.744542+00:00
-- url     : https://prove2.me/theorems/d188034f-f698-4f19-b1f8-12e8b74d8a9d
-- title:
--   One-year innovation second moment has discrete survival factor
-- statement:
--   The second moment of centred death indicator is D_t p_t; this is the characteristic discrete Hattendorff survival factor.
--
--   **Mathematical statement**
--
--   $$
--   \mathbb E_w[I_t^2]=D_tp_t
--   $$
-- source:
--   Shiu and Xiong (2021), An elementary derivation of Hattendorff's theorem, European Actuarial Journal 11, 319-323, equations (1)-(3), https://doi.org/10.1007/s13385-020-00256-9; Gerber (1997), Life Insurance Mathematics, 3rd ed., Ch.6 Sec.6.7; Gerber Leung Shiu (2003), Indicator Function and Hattendorff Theorem, https://doi.org/10.1080/10920277.2003.10596075

import Mathlib
import Definitions.Def_actuarial_finiteMortalityDeathMass
import Definitions.Def_actuarial_finiteMortalityInnovation
import Definitions.Def_actuarial_finiteMortalitySurvivalMass
import Definitions.Def_actuarial_finiteMortalitySurvivalRate
open MeasureTheory

namespace ActuarialValuation

theorem finiteMortalityInnovation_secondMoment {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (K : Ω → ℕ) (t : ℕ) (hw : ∀ ω, 0 ≤ w ω)
  (hS : 0 < finiteMortalitySurvivalMass w K t)
  :
  (∑ ω : Ω, w ω * (finiteMortalityInnovation w K t ω) ^ 2) =
    finiteMortalityDeathMass w K t * finiteMortalitySurvivalRate w K t := by sorry

end ActuarialValuation
