-- Prove2me | Theorems.Thm_ActuarialValuation_finiteLifeInForceIndicator_after_death
-- name    : ActuarialValuation.finiteLifeInForceIndicator_after_death
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T08:57:25.493979+00:00
-- url     : https://prove2.me/theorems/fa3b0197-31cd-4714-9fad-bf04c49efbd4
-- title:
--   No in-force indicator beyond death year
-- statement:
--   Once time t strictly exceeds the curtate death year K, the in-force indicator vanishes.
--
--   **Mathematical statement**
--
--   $$
--   t>K\implies S_t(K)=0
--   $$
-- source:
--   Shiu and Xiong (2021), An elementary derivation of Hattendorff's theorem, European Actuarial Journal 11 319-323, especially equations (1), (3)-(5), https://doi.org/10.1007/s13385-020-00256-9; Gerber (1997), Life Insurance Mathematics, third ed., Chapter 6 section 6.7, https://doi.org/10.1007/978-3-662-03460-6

import Mathlib
import Definitions.Def_actuarial_finiteLifeInForceIndicator
open MeasureTheory

namespace ActuarialValuation

theorem finiteLifeInForceIndicator_after_death (K t : ℕ) (h : K < t)
  :
  finiteLifeInForceIndicator K t = 0 := by sorry

end ActuarialValuation
