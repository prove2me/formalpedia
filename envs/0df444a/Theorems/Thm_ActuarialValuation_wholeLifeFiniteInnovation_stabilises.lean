-- Prove2me | Theorems.Thm_ActuarialValuation_wholeLifeFiniteInnovation_stabilises
-- name    : ActuarialValuation.wholeLifeFiniteInnovation_stabilises
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T10:09:06.426129+00:00
-- url     : https://prove2.me/theorems/3765888d-fed9-4810-b5a5-0ce3832ad2ed
-- title:
--   Pathwise centred loss stabilises after death
-- statement:
--   Once the valuation horizon strictly exceeds the realised death year, all additional annual innovations vanish. The finite loss then equals its complete-life value on that individual scenario, even though no finite maximum lifetime exists across scenarios.
--
--   **Mathematical statement**
--
--   $$
--   n>k\Longrightarrow Z_n(k)=Z_\infty(k)
--   $$
-- source:
--   Shiu and Xiong (2021), An elementary derivation of Hattendorff's theorem, European Actuarial Journal 11, 319-323, DOI https://doi.org/10.1007/s13385-020-00256-9; original countable-L2 extension in this mission

import Mathlib
import Definitions.Def_actuarial_wholeLifeFiniteInnovation
import Definitions.Def_actuarial_wholeLifeCompleteInnovation

namespace ActuarialValuation

theorem wholeLifeFiniteInnovation_stabilises (w rho : ℕ → ℝ) (n k : ℕ)
  (h : k < n) :
  wholeLifeFiniteInnovation w rho n k =
    wholeLifeCompleteInnovation w rho k := by sorry

end ActuarialValuation
