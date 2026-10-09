-- Prove2me | Theorems.Thm_ActuarialValuation_temporaryAnnuityImmediate_eq_sum
-- name    : ActuarialValuation.temporaryAnnuityImmediate_eq_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T20:10:12.605496+00:00
-- url     : https://prove2.me/theorems/cf2c01c4-ca1d-44db-9655-0cc1f958f267
-- title:
--   Temporary annuity-immediate present value as a finite survival sum
-- statement:
--   The annuity-immediate present value equals the finite sum of discounted end-year payments, each conditional on survival to that payment date. When the term is zero the sum vanishes, and when it is one the sole payment is at time one.
--
--   **Mathematical statement**
--
--   $$
--   Z_{\mathrm{immediate}}=\sum_{k=0}^{n-1}v^{k+1}\mathbf1_{S_{k+1}}
--   $$
-- source:
--   *Life Contingencies*, Chapter 3 §3.3.2, equation (3.16), https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib
import Definitions.Def_actuarial_temporaryAnnuityImmediatePV
import Definitions.Def_actuarial_curtateSurvivalEvent
open MeasureTheory

namespace ActuarialValuation

theorem temporaryAnnuityImmediate_eq_sum {Ω : Type*} (K : Ω → ℕ) (v : ℝ) (n : ℕ) (ω : Ω)
    :
    temporaryAnnuityImmediatePV K v n ω = ∑ k ∈ Finset.range n, v ^ (k + 1) * (curtateSurvivalEvent K (k + 1)).indicator (fun _ : Ω => (1 : ℝ)) ω := by sorry

end ActuarialValuation
