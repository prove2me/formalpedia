-- Prove2me | Theorems.Thm_ActuarialValuation_curtateSurvivalEvent_antitone
-- name    : ActuarialValuation.curtateSurvivalEvent_antitone
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T20:06:07.120845+00:00
-- url     : https://prove2.me/theorems/f5966926-17d9-468e-a3b1-d1295bf908d7
-- title:
--   Survival events shrink at later dates
-- statement:
--   Survival to a later policy date entails survival to every earlier date, so the event of survival to the later date is contained in the event of survival to the earlier date.
--
--   **Mathematical statement**
--
--   $$
--   i\le j\Longrightarrow S_j\subseteq S_i
--   $$
-- source:
--   Derived from survival indicators in Chapter 3 §§3.1.1, 3.3.2, https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib
import Definitions.Def_actuarial_curtateSurvivalEvent
open MeasureTheory

namespace ActuarialValuation

theorem curtateSurvivalEvent_antitone {Ω : Type*} (K : Ω → ℕ) (i j : ℕ) (hij : i ≤ j)
    :
    curtateSurvivalEvent K j ⊆ curtateSurvivalEvent K i := by sorry

end ActuarialValuation
