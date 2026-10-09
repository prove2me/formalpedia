-- Prove2me | Theorems.Thm_ActuarialValuation_deferredDue_eq_survival_tsum
-- name    : ActuarialValuation.deferredDue_eq_survival_tsum
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T21:20:17.279234+00:00
-- url     : https://prove2.me/theorems/cc6ea602-0fc7-4729-b17c-031f5c7f7c02
-- title:
--   Deferred due PV equals its survival-weighted tail
-- statement:
--   For a realised finite curtate lifetime K, the deferred due present value is the survival-indicator sum over dates n through K, with no payments before n. This expresses the deferred tail in textbook equations (3.17)–(3.18).
--
--   **Mathematical statement**
--
--   $$
--   Z_{\mathrm{deferred,due}}=\sum_{k=n}^{\infty}v^k\mathbf1_{\{K\ge k\}}
--   $$
-- source:
--   *Life Contingencies*, Chapter 3 §3.3.3 eqs (3.17)–(3.18), https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib
import Definitions.Def_actuarial_curtateSurvivalEvent
import Definitions.Def_actuarial_deferredAnnuityDuePV
open MeasureTheory

namespace ActuarialValuation

theorem deferredDue_eq_survival_tsum {Ω : Type*} (K : Ω → ℕ) (v : ℝ) (n : ℕ) (ω : Ω)
    :
    deferredAnnuityDuePV K v n ω = ∑' k : ℕ, if n ≤ k then v ^ k * (curtateSurvivalEvent K k).indicator (fun _ : Ω => (1 : ℝ)) ω else 0 := by sorry

end ActuarialValuation
