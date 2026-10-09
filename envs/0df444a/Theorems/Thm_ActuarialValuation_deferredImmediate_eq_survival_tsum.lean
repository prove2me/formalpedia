-- Prove2me | Theorems.Thm_ActuarialValuation_deferredImmediate_eq_survival_tsum
-- name    : ActuarialValuation.deferredImmediate_eq_survival_tsum
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T21:20:59.800514+00:00
-- url     : https://prove2.me/theorems/7b067487-1038-439b-847e-9197ee293235
-- title:
--   Deferred immediate PV equals its survival-weighted tail
-- statement:
--   For a realised finite curtate lifetime K, the deferred immediate present value is the survival-indicator sum over dates n plus one through K. The first n end-year dates are excluded, as in textbook equations (3.17)–(3.18).
--
--   **Mathematical statement**
--
--   $$
--   Z_{\mathrm{deferred,immediate}}=\sum_{k=n}^{\infty}v^{k+1}\mathbf1_{\{K\ge k+1\}}
--   $$
-- source:
--   *Life Contingencies*, Chapter 3 §3.3.3 eqs (3.17)–(3.18), https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib
import Definitions.Def_actuarial_curtateSurvivalEvent
import Definitions.Def_actuarial_deferredAnnuityImmediatePV
open MeasureTheory

namespace ActuarialValuation

theorem deferredImmediate_eq_survival_tsum {Ω : Type*} (K : Ω → ℕ) (v : ℝ) (n : ℕ) (ω : Ω)
    :
    deferredAnnuityImmediatePV K v n ω = ∑' k : ℕ, if n ≤ k then v ^ (k + 1) * (curtateSurvivalEvent K (k + 1)).indicator (fun _ : Ω => (1 : ℝ)) ω else 0 := by sorry

end ActuarialValuation
