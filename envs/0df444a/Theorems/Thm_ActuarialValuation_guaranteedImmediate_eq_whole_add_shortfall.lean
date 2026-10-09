-- Prove2me | Theorems.Thm_ActuarialValuation_guaranteedImmediate_eq_whole_add_shortfall
-- name    : ActuarialValuation.guaranteedImmediate_eq_whole_add_shortfall
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T21:35:20.625581+00:00
-- url     : https://prove2.me/theorems/dbf4ddde-72d6-4869-b015-fc40f54045ea
-- title:
--   Guaranteed immediate eq whole add shortfall
-- statement:
--   States the corresponding whole-life comparison for an immediate annuity, adding the payments needed when survival ends before the guarantee is fulfilled.
--
--   **Mathematical statement**
--
--   $$
--   Z_{\mathrm{guaranteed,immediate}}=Z_{\mathrm{whole,immediate}}+\sum_{k=0}^{n-1}v^{k+1}\mathbf1_{\{K<k+1\}}
--   $$
-- source:
--   Derived from Life Contingencies §3.3.4, equations (3.19)-(3.20), together with §3.1.1, equations (3.3), (3.5)-(3.6); https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib
import Definitions.Def_actuarial_wholeLifeAnnuityDuePV
import Definitions.Def_actuarial_wholeLifeAnnuityImmediatePV
import Definitions.Def_actuarial_deferredAnnuityDuePV
import Definitions.Def_actuarial_deferredAnnuityImmediatePV
import Definitions.Def_actuarial_curtateSurvivalEvent
import Definitions.Def_actuarial_annuityCertainDuePV
import Definitions.Def_actuarial_annuityCertainImmediatePV
import Definitions.Def_actuarial_guaranteedAnnuityDuePV
import Definitions.Def_actuarial_guaranteedAnnuityImmediatePV
open MeasureTheory

namespace ActuarialValuation

theorem guaranteedImmediate_eq_whole_add_shortfall {Ω : Type*} (K : Ω → ℕ) (v : ℝ) (n : ℕ) (ω : Ω)
    :
    guaranteedAnnuityImmediatePV K v n ω =
      wholeLifeAnnuityImmediatePV K v ω +
      (∑ k ∈ Finset.range n, if K ω < k + 1 then v ^ (k + 1) else 0) := by sorry

end ActuarialValuation
