-- Prove2me | Theorems.Thm_ActuarialValuation_deathYearEvent_disjoint
-- name    : ActuarialValuation.deathYearEvent_disjoint
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T17:54:24.839105+00:00
-- url     : https://prove2.me/theorems/440041f2-e471-43c9-915b-4a35ee2e2bb5
-- title:
--   Death cannot occur in two different policy years
-- statement:
--   Establish that distinct policy-year death events are pairwise disjoint for one life.
--
--   **Mathematical statement**
--
--   $$
--   i\ne j\Longrightarrow D_i\cap D_j=\varnothing
--   $$
-- source:
--   Chapter 3 §3.1.1 (3.4), §3.2.2 (3.8), https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html.

import Mathlib
import Definitions.Def_actuarial_deathYearEvent

namespace ActuarialValuation
theorem deathYearEvent_disjoint {Ω : Type*} (K : Ω → ℕ)
    (i j : ℕ) (hij : i ≠ j)
    :
    Disjoint (deathYearEvent K i) (deathYearEvent K j) := by sorry
end ActuarialValuation
