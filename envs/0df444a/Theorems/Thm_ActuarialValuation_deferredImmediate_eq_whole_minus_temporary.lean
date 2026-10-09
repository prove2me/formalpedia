-- Prove2me | Theorems.Thm_ActuarialValuation_deferredImmediate_eq_whole_minus_temporary
-- name    : ActuarialValuation.deferredImmediate_eq_whole_minus_temporary
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T21:28:20.355016+00:00
-- url     : https://prove2.me/theorems/a05568d8-fd9e-49d1-9a1b-5b109bf36160
-- title:
--   Deferred immediate PV equals whole-life immediate less the temporary prefix
-- statement:
--   For each realised lifetime, removing the first n immediate payments, at times 1 through n, from the whole-life immediate present value leaves the deferred immediate schedule starting at n plus one. This is a derived bridge between textbook equations (3.11)–(3.12), the temporary-annuity prefix in (3.15)–(3.16), and the deferred result in (3.17)–(3.18).
--
--   **Mathematical statement**
--
--   $$
--   Z_{\mathrm{deferred,immediate}}=Z_{\mathrm{WL,immediate}}-\sum_{k=0}^{n-1}v^{k+1}\mathbf1_{\{K\ge k+1\}}
--   $$
-- source:
--   Derived identity relating §3.3.1 and §3.3.3 to §3.3.2 (3.15)–(3.16), https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib
import Definitions.Def_actuarial_curtateSurvivalEvent
import Definitions.Def_actuarial_wholeLifeAnnuityImmediatePV
import Definitions.Def_actuarial_deferredAnnuityImmediatePV
open MeasureTheory

namespace ActuarialValuation

theorem deferredImmediate_eq_whole_minus_temporary {Ω : Type*} (K : Ω → ℕ) (v : ℝ) (n : ℕ) (ω : Ω)
    :
    deferredAnnuityImmediatePV K v n ω = wholeLifeAnnuityImmediatePV K v ω - (∑ k ∈ Finset.range n, v ^ (k + 1) * (curtateSurvivalEvent K (k + 1)).indicator (fun _ : Ω => (1 : ℝ)) ω) := by sorry

end ActuarialValuation
