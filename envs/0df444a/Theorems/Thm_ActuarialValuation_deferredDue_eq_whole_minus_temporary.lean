-- Prove2me | Theorems.Thm_ActuarialValuation_deferredDue_eq_whole_minus_temporary
-- name    : ActuarialValuation.deferredDue_eq_whole_minus_temporary
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T21:23:36.504143+00:00
-- url     : https://prove2.me/theorems/78410b30-6429-4cc2-bae8-c55ad275ac30
-- title:
--   Deferred due PV equals whole-life due less the temporary prefix
-- statement:
--   For each realised lifetime, removing the first n due payments, at times 0 through n minus one, from the whole-life due present value leaves the deferred due schedule starting at n. This is a derived bridge between textbook equations (3.11)–(3.12), the temporary-annuity prefix in (3.15)–(3.16), and the deferred result in (3.17)–(3.18).
--
--   **Mathematical statement**
--
--   $$
--   Z_{\mathrm{deferred,due}}=Z_{\mathrm{WL,due}}-\sum_{k=0}^{n-1}v^k\mathbf1_{\{K\ge k\}}
--   $$
-- source:
--   Derived identity relating §3.3.1 and §3.3.3 to §3.3.2 (3.15)–(3.16), https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib
import Definitions.Def_actuarial_curtateSurvivalEvent
import Definitions.Def_actuarial_wholeLifeAnnuityDuePV
import Definitions.Def_actuarial_deferredAnnuityDuePV
open MeasureTheory

namespace ActuarialValuation

theorem deferredDue_eq_whole_minus_temporary {Ω : Type*} (K : Ω → ℕ) (v : ℝ) (n : ℕ) (ω : Ω)
    :
    deferredAnnuityDuePV K v n ω = wholeLifeAnnuityDuePV K v ω - (∑ k ∈ Finset.range n, v ^ k * (curtateSurvivalEvent K k).indicator (fun _ : Ω => (1 : ℝ)) ω) := by sorry

end ActuarialValuation
