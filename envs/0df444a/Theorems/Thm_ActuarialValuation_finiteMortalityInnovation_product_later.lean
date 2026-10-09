-- Prove2me | Theorems.Thm_ActuarialValuation_finiteMortalityInnovation_product_later
-- name    : ActuarialValuation.finiteMortalityInnovation_product_later
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T07:19:26.162246+00:00
-- url     : https://prove2.me/theorems/03cd234c-6b64-481e-970d-60f01fbfefaf
-- title:
--   Earlier mortality shock on support of later shock
-- statement:
--   A later nonzero shock requires survival past i, when the earlier shock is the negative conditional death rate.
--
--   **Mathematical statement**
--
--   $$
--   i<j\Rightarrow I_iI_j=-q_iI_j
--   $$
-- source:
--   Shiu and Xiong (2021), An elementary derivation of Hattendorff's theorem, European Actuarial Journal 11, 319-323, equations (1)-(3), https://doi.org/10.1007/s13385-020-00256-9; Gerber (1997), Life Insurance Mathematics, 3rd ed., Ch.6 Sec.6.7; Gerber Leung Shiu (2003), Indicator Function and Hattendorff Theorem, https://doi.org/10.1080/10920277.2003.10596075

import Mathlib
import Definitions.Def_actuarial_finiteMortalityDeathRate
import Definitions.Def_actuarial_finiteMortalityInnovation
open MeasureTheory

namespace ActuarialValuation

theorem finiteMortalityInnovation_product_later {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (K : Ω → ℕ) (i j : ℕ) (ω : Ω) (hij : i < j)
  :
  finiteMortalityInnovation w K i ω * finiteMortalityInnovation w K j ω =
    -(finiteMortalityDeathRate w K i) * finiteMortalityInnovation w K j ω := by sorry

end ActuarialValuation
