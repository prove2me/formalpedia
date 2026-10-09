-- Prove2me | Theorems.Thm_ActuarialValuation_guaranteedDue_eq_whole_add_shortfall
-- name    : ActuarialValuation.guaranteedDue_eq_whole_add_shortfall
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T21:32:53.201295+00:00
-- url     : https://prove2.me/theorems/d9d6228b-5233-462c-995e-2fb3534bd7b5
-- title:
--   Guaranteed due eq whole add shortfall
-- statement:
--   States that the due guaranteed value equals the whole-life due value plus payments needed to cover the shortfall when survival ends before the guarantee is fulfilled.
--
--   **Mathematical statement**
--
--   $$
--   Z_{\mathrm{guaranteed,due}}=Z_{\mathrm{whole,due}}+\sum_{k=0}^{n-1}v^k\mathbf1_{\{K<k\}}
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

theorem guaranteedDue_eq_whole_add_shortfall {Ω : Type*} (K : Ω → ℕ) (v : ℝ) (n : ℕ) (ω : Ω)
    :
    guaranteedAnnuityDuePV K v n ω =
      wholeLifeAnnuityDuePV K v ω +
      (∑ k ∈ Finset.range n, if K ω < k then v ^ k else 0) := by sorry

end ActuarialValuation
