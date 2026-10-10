-- Prove2me | Theorems.Thm_ActuarialValuation_discountedAnnualGainSum_zero_term
-- name    : ActuarialValuation.discountedAnnualGainSum_zero_term
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T23:27:44.644972+00:00
-- url     : https://prove2.me/theorems/649c359f-a1ee-439d-b817-6889f3425ca3
-- title:
--   An empty annual gain series totals zero
-- statement:
--   No years means no discounted cashflow contributions.
--
--   **Mathematical statement**
--
--   $$
--   L_0=0
--   $$
-- source:
--   Gerber (1997), Life Insurance Mathematics, third edition, §6.7 equations (6.7.3), (6.7.6)-(6.7.10); Bladt et al., An elementary derivation of Hattendorff's theorem (2021), https://doi.org/10.1007/s13385-020-00256-9; R. Norberg (1992), Hattendorff's theorem and Thiele's differential equation generalized, https://doi.org/10.1080/03461238.1992.10413894

import Mathlib
import Definitions.Def_actuarial_discountedAnnualGainSum
open MeasureTheory

namespace ActuarialValuation

theorem discountedAnnualGainSum_zero_term {Ω : Type*} (G : ℕ → Ω → ℝ) (v : ℝ) (ω : Ω)
  :
  discountedAnnualGainSum G v 0 ω = 0 := by sorry

end ActuarialValuation
