-- Prove2me | Theorems.Thm_ActuarialValuation_wholeLifeTailMass_zero
-- name    : ActuarialValuation.wholeLifeTailMass_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T10:03:20.446116+00:00
-- url     : https://prove2.me/theorems/b581b8d4-4800-42ed-bdc4-f0f36074c57c
-- title:
--   At policy issue, total survival mass equals one
-- statement:
--   Every natural-number-valued death year is at least zero. Thus the countable tail mass at time zero is the complete death-year distribution and, under the supplied normalisation, equals one.
--
--   **Mathematical statement**
--
--   $$
--   S_0=1
--   $$
-- source:
--   Shiu and Xiong (2021), An elementary derivation of Hattendorff's theorem, European Actuarial Journal 11, 319-323, DOI https://doi.org/10.1007/s13385-020-00256-9; original countable-L2 extension in this mission

import Mathlib
import Definitions.Def_actuarial_wholeLifeTailMass

namespace ActuarialValuation

theorem wholeLifeTailMass_zero (w : ℕ → ℝ)
  (h : (∑' k : ℕ, w k) = 1) :
  wholeLifeTailMass w 0 = 1 := by sorry

end ActuarialValuation
