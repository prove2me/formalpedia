-- Prove2me | Theorems.Thm_ActuarialValuation_finiteReserveLoss_HattendorffBridge_fundamental
-- name    : ActuarialValuation.finiteReserveLoss_HattendorffBridge_fundamental
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T09:16:20.904247+00:00
-- url     : https://prove2.me/theorems/424d49d1-611f-4c29-b634-726ed25a0402
-- title:
--   Fully discrete insurer loss equals reserve plus mortality innovations
-- statement:
--   Under the reserve recursion and annual survival/death normalisation, finite-horizon insurer loss including the terminal liability equals the opening reserve plus the discounted net-amount-at-risk mortality-innovation sum, pathwise for every curtate death year K.
--
--   **Mathematical statement**
--
--   $$
--   L_n(K)-V_0=\sum_{t<n}v^{t+1}(b_{t+1}-V_{t+1})I_t(K)
--   $$
-- source:
--   Shiu and Xiong (2021), An elementary derivation of Hattendorff's theorem, European Actuarial Journal 11 319-323, especially equations (1), (3)-(5), https://doi.org/10.1007/s13385-020-00256-9; Gerber (1997), Life Insurance Mathematics, third ed., Chapter 6 section 6.7, https://doi.org/10.1007/978-3-662-03460-6

import Mathlib
import Definitions.Def_actuarial_finiteReserveAnnualBalance
import Definitions.Def_actuarial_finiteReserveInnovationValue
import Definitions.Def_actuarial_finiteReserveLossAtIssue
open MeasureTheory

namespace ActuarialValuation

theorem finiteReserveLoss_HattendorffBridge_fundamental (K n : ℕ) (v : ℝ) (reserve premium benefit p q : ℕ → ℝ)
  (hPQ : ∀ t ∈ Finset.range n, p t + q t = 1)
  (hR : ∀ t ∈ Finset.range n, finiteReserveAnnualBalance v reserve premium benefit p q t)
  :
  finiteReserveLossAtIssue K n v premium benefit reserve =
  reserve 0 + finiteReserveInnovationValue K n v benefit reserve q := by sorry

end ActuarialValuation
