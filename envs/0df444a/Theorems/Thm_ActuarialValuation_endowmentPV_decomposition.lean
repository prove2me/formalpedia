-- Prove2me | Theorems.Thm_ActuarialValuation_endowmentPV_decomposition
-- name    : ActuarialValuation.endowmentPV_decomposition
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T19:57:28.730774+00:00
-- url     : https://prove2.me/theorems/ec7eea18-e19f-4b8b-b9ec-b8fea5990b65
-- title:
--   Endowment equals term assurance plus maturity benefit
-- statement:
--   The endowment present value is the sum of the term assurance payment at the end of the year of death and the curtate maturity payment. The payment events are disjoint, with maturity governed by K being at least n.
--
--   **Mathematical statement**
--
--   $$
--   Z_{\mathrm{endow}}=Z_{\mathrm{term}}+v^n\mathbf1_{\{K\ge n\}}
--   $$
-- source:
--   *Life Contingencies*, Chapter 3 §3.2.4, equation (3.10), https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib
import Definitions.Def_actuarial_endowmentAssurancePV
import Definitions.Def_actuarial_curtatePureEndowmentPV
import Definitions.Def_actuarial_curtateSurvivalEvent
import Definitions.Def_actuarial_termAssurancePV
open MeasureTheory

namespace ActuarialValuation

theorem endowmentPV_decomposition {Ω : Type*} (K : Ω → ℕ) (v : ℝ) (n : ℕ)
    (ω : Ω)
    : endowmentAssurancePV K v n ω = termAssurancePV K v n ω + curtatePureEndowmentPV K v n ω := by sorry

end ActuarialValuation
