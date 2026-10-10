-- Prove2me | Theorems.Thm_ActuarialValuation_wholeLifeYearInnovation_orthogonal
-- name    : ActuarialValuation.wholeLifeYearInnovation_orthogonal
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T10:09:51.778883+00:00
-- url     : https://prove2.me/theorems/a0603775-994c-4adf-b3d8-b5768671c220
-- title:
--   Different yearly mortality surprises are orthogonal
-- statement:
--   A contribution to the later year j requires survival through the earlier year i. Conditional on that earlier survival, the future death-year innovation is centred, so distinct policy-year mortality shocks have zero weighted cross-moment. They need not be independent.
--
--   **Mathematical statement**
--
--   $$
--   i<j\Longrightarrow \mathbb E[I_i I_j]=0
--   $$
-- source:
--   Shiu and Xiong (2021), An elementary derivation of Hattendorff's theorem, European Actuarial Journal 11, 319-323, DOI https://doi.org/10.1007/s13385-020-00256-9; original countable-L2 extension in this mission

import Mathlib
import Definitions.Def_actuarial_wholeLifeYearInnovation
import Definitions.Def_actuarial_wholeLifeTailMass

namespace ActuarialValuation

theorem wholeLifeYearInnovation_orthogonal (w : ℕ → ℝ) (i j : ℕ)
  (hw : Summable w) (hi : i < j)
  (hSi : 0 < wholeLifeTailMass w i)
  (hSj : 0 < wholeLifeTailMass w j) :
  (∑' k : ℕ, w k *
    wholeLifeYearInnovation w i k * wholeLifeYearInnovation w j k) = 0 := by sorry

end ActuarialValuation
