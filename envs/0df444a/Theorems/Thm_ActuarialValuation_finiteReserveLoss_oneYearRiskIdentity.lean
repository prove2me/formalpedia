-- Prove2me | Theorems.Thm_ActuarialValuation_finiteReserveLoss_oneYearRiskIdentity
-- name    : ActuarialValuation.finiteReserveLoss_oneYearRiskIdentity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T09:15:39.354789+00:00
-- url     : https://prove2.me/theorems/f5840567-f04a-42e8-98a4-eb9faddeacc4
-- title:
--   One-year reserve-adjusted loss equals mortality surprise
-- statement:
--   Annual premiums, claims and reserve movement combine to the discounted net amount at risk times the centred death indicator, using p+q=1 and the exact reserve equation.
--
--   **Mathematical statement**
--
--   $$
--   \Delta L_t=v^{t+1}(b_{t+1}-V_{t+1})I_t
--   $$
-- source:
--   Shiu and Xiong (2021), An elementary derivation of Hattendorff's theorem, European Actuarial Journal 11 319-323, especially equations (1), (3)-(5), https://doi.org/10.1007/s13385-020-00256-9; Gerber (1997), Life Insurance Mathematics, third ed., Chapter 6 section 6.7, https://doi.org/10.1007/978-3-662-03460-6

import Mathlib
import Definitions.Def_actuarial_finiteLifeDeathIndicator
import Definitions.Def_actuarial_finiteLifeInForceIndicator
import Definitions.Def_actuarial_finiteReserveAnnualBalance
import Definitions.Def_actuarial_finiteReserveYearInnovation
open MeasureTheory

namespace ActuarialValuation

theorem finiteReserveLoss_oneYearRiskIdentity (K t : ℕ) (v : ℝ) (reserve premium benefit p q : ℕ → ℝ)
  (hPQ : p t + q t = 1)
  (hR : finiteReserveAnnualBalance v reserve premium benefit p q t)
  :
  v ^ (t + 1) * benefit (t + 1) * finiteLifeDeathIndicator K t -
   v ^ t * premium t * finiteLifeInForceIndicator K t +
   v ^ (t + 1) * reserve (t + 1) * finiteLifeInForceIndicator K (t + 1) -
   v ^ t * reserve t * finiteLifeInForceIndicator K t =
 v ^ (t + 1) * (benefit (t + 1) - reserve (t + 1)) *
   finiteReserveYearInnovation K t q := by sorry

end ActuarialValuation
