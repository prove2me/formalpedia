-- Prove2me | Theorems.Thm_ActuarialValuation_annualReserveGain_discounted_telescope
-- name    : ActuarialValuation.annualReserveGain_discounted_telescope
-- status  : Open
-- author  : @WillR
-- created : 2026-10-08T23:35:34.891981+00:00
-- url     : https://prove2.me/theorems/2e44bd78-c946-4b5e-aede-650bffee1d9b
-- title:
--   Discounted annual gains telescope to cashflow plus reserve release
-- statement:
--   Discounted reserve additions and releases telescope across policy years, leaving the terminal discounted reserve less the initial reserve.
--
--   **Mathematical statement**
--
--   $$
--   \sum_{k<n}v^kG_k=\sum_{k<n}v^kC_k+v^nR_n-R_0
--   $$
-- source:
--   Gerber (1997), Life Insurance Mathematics, third edition, §6.7 equations (6.7.3), (6.7.6)-(6.7.10); Bladt et al., An elementary derivation of Hattendorff's theorem (2021), https://doi.org/10.1007/s13385-020-00256-9; R. Norberg (1992), Hattendorff's theorem and Thiele's differential equation generalized, https://doi.org/10.1080/03461238.1992.10413894

import Mathlib
import Definitions.Def_actuarial_annualReserveGain
import Definitions.Def_actuarial_discountedAnnualGainSum
open MeasureTheory

namespace ActuarialValuation

theorem annualReserveGain_discounted_telescope {Ω : Type*} (C : ℕ → Ω → ℝ) (R : ℕ → ℝ)
  (v : ℝ) (n : ℕ) (ω : Ω)
  :
  discountedAnnualGainSum (annualReserveGain C R v) v n ω =
    discountedAnnualGainSum C v n ω + v ^ n * R n - R 0 := by sorry

end ActuarialValuation
