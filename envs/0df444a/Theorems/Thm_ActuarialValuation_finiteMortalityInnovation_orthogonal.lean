-- Prove2me | Theorems.Thm_ActuarialValuation_finiteMortalityInnovation_orthogonal
-- name    : ActuarialValuation.finiteMortalityInnovation_orthogonal
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T07:22:32.587086+00:00
-- url     : https://prove2.me/theorems/4c6e6852-00dc-407e-a35b-877f4587b6fb
-- title:
--   Distinct annual mortality shocks are uncorrelated by mortality structure
-- statement:
--   Earlier innovation times later innovation is proportional to the later centred shock; the weighted cross moment vanishes.
--
--   **Mathematical statement**
--
--   $$
--   i<j\Rightarrow\mathbb E_w[I_iI_j]=0
--   $$
-- source:
--   Shiu and Xiong (2021), An elementary derivation of Hattendorff's theorem, European Actuarial Journal 11, 319-323, equations (1)-(3), https://doi.org/10.1007/s13385-020-00256-9; Gerber (1997), Life Insurance Mathematics, 3rd ed., Ch.6 Sec.6.7; Gerber Leung Shiu (2003), Indicator Function and Hattendorff Theorem, https://doi.org/10.1080/10920277.2003.10596075

import Mathlib
import Definitions.Def_actuarial_finiteMortalityInnovation
import Definitions.Def_actuarial_finiteMortalitySurvivalMass
open MeasureTheory

namespace ActuarialValuation

theorem finiteMortalityInnovation_orthogonal {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (K : Ω → ℕ) (i j : ℕ) (hij : i < j) (hSj : 0 < finiteMortalitySurvivalMass w K j)
  :
  (∑ ω : Ω, w ω * finiteMortalityInnovation w K i ω * finiteMortalityInnovation w K j ω) = 0 := by sorry

end ActuarialValuation
