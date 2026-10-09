-- Prove2me | Theorems.Thm_ActuarialValuation_temporaryAnnuityDue_eq_sum
-- name    : ActuarialValuation.temporaryAnnuityDue_eq_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T20:09:09.805462+00:00
-- url     : https://prove2.me/theorems/94c4c3d7-4cab-46ee-a70f-25f91123e76f
-- title:
--   Temporary annuity-due present value as a finite survival sum
-- statement:
--   The annuity-due present value equals the finite sum of discounted payments at times zero through one year before the term ends, with each payment conditional on survival to its time. When the term is zero the sum vanishes, and when it is one the sole payment is at time zero.
--
--   **Mathematical statement**
--
--   $$
--   Z_{\mathrm{due}}=\sum_{k=0}^{n-1}v^k\mathbf1_{S_k}
--   $$
-- source:
--   *Life Contingencies*, Chapter 3 §3.3.2, equation (3.15), https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib
import Definitions.Def_actuarial_temporaryAnnuityDuePV
import Definitions.Def_actuarial_curtateSurvivalEvent
open MeasureTheory

namespace ActuarialValuation

theorem temporaryAnnuityDue_eq_sum {Ω : Type*} (K : Ω → ℕ) (v : ℝ) (n : ℕ) (ω : Ω)
    :
    temporaryAnnuityDuePV K v n ω = ∑ k ∈ Finset.range n, v ^ k * (curtateSurvivalEvent K k).indicator (fun _ : Ω => (1 : ℝ)) ω := by sorry

end ActuarialValuation
