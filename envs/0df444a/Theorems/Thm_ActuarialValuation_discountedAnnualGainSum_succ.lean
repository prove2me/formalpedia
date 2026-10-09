-- Prove2me | Theorems.Thm_ActuarialValuation_discountedAnnualGainSum_succ
-- name    : ActuarialValuation.discountedAnnualGainSum_succ
-- status  : Open
-- author  : @WillR
-- created : 2026-10-08T23:29:23.257531+00:00
-- url     : https://prove2.me/theorems/f059519a-21bf-4fa2-a36d-c830e4d8607a
-- title:
--   Discounted gain aggregation adds one year
-- statement:
--   The finite annual value of n+1 years extends the first n years by the time-n gain.
--
--   **Mathematical statement**
--
--   $$
--   L_{n+1}=L_n+v^nG_n
--   $$
-- source:
--   Gerber (1997), Life Insurance Mathematics, third edition, §6.7 equations (6.7.3), (6.7.6)-(6.7.10); Bladt et al., An elementary derivation of Hattendorff's theorem (2021), https://doi.org/10.1007/s13385-020-00256-9; R. Norberg (1992), Hattendorff's theorem and Thiele's differential equation generalized, https://doi.org/10.1080/03461238.1992.10413894

import Mathlib
import Definitions.Def_actuarial_discountedAnnualGainSum
open MeasureTheory

namespace ActuarialValuation

theorem discountedAnnualGainSum_succ {Ω : Type*} (G : ℕ → Ω → ℝ) (v : ℝ) (n : ℕ) (ω : Ω)
  :
  discountedAnnualGainSum G v (n + 1) ω =
    discountedAnnualGainSum G v n ω + v ^ n * G n ω := by sorry

end ActuarialValuation
