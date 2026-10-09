-- Prove2me | Theorems.Thm_ActuarialValuation_curtateSurvivalEvent_inter
-- name    : ActuarialValuation.curtateSurvivalEvent_inter
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T20:06:28.660328+00:00
-- url     : https://prove2.me/theorems/366d51ca-82a3-4d0c-9844-0264b50e0f29
-- title:
--   Intersection of survival events equals later survival
-- statement:
--   The intersection of survival requirements at two dates is exactly the requirement to survive to the later date.
--
--   **Mathematical statement**
--
--   $$
--   S_i\cap S_j=S_{\max(i,j)}
--   $$
-- source:
--   Derived from survival indicators in Chapter 3 §§3.1.1, 3.3.2, https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib
import Definitions.Def_actuarial_curtateSurvivalEvent
open MeasureTheory

namespace ActuarialValuation

theorem curtateSurvivalEvent_inter {Ω : Type*} (K : Ω → ℕ) (i j : ℕ)
    :
    curtateSurvivalEvent K i ∩ curtateSurvivalEvent K j = curtateSurvivalEvent K (max i j) := by sorry

end ActuarialValuation
