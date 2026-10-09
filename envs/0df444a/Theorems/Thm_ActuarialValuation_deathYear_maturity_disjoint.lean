-- Prove2me | Theorems.Thm_ActuarialValuation_deathYear_maturity_disjoint
-- name    : ActuarialValuation.deathYear_maturity_disjoint
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T19:18:39.376461+00:00
-- url     : https://prove2.me/theorems/234e05bd-e811-4190-b2fb-37e596f38d32
-- title:
--   Death in term and survival to maturity are disjoint
-- statement:
--   A death-year benefit within the term and a maturity benefit cannot both be paid to the same life. The two payment events are disjoint.
--
--   **Mathematical statement**
--
--   $$
--   k<n\implies \{K=k\}\cap\{K\ge n\}=\varnothing
--   $$
-- source:
--   *Life Contingencies*, Chapter 3 §3.2.4, equation (3.10), https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib
import Definitions.Def_actuarial_curtateSurvivalEvent
import Definitions.Def_actuarial_deathYearEvent
open MeasureTheory

namespace ActuarialValuation

theorem deathYear_maturity_disjoint {Ω : Type*} (K : Ω → ℕ) (k n : ℕ) (hk : k < n)
    : Disjoint (deathYearEvent K k) (curtateSurvivalEvent K n) := by sorry

end ActuarialValuation
