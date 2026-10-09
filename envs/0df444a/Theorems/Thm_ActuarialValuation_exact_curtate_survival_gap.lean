-- Prove2me | Theorems.Thm_ActuarialValuation_exact_curtate_survival_gap
-- name    : ActuarialValuation.exact_curtate_survival_gap
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T19:18:03.361196+00:00
-- url     : https://prove2.me/theorems/4ca7dd70-6aaf-49eb-aa8a-eaf67386af3d
-- title:
--   Exact and curtate survival differ only at the boundary
-- statement:
--   The event that exact lifetime exceeds the term is contained in the event that curtate lifetime is at least the term. Their difference consists of lives dying exactly at maturity, so the events agree only after accounting for that boundary.
--
--   **Mathematical statement**
--
--   $$
--   \{K\ge n\}=\{T>n\}\cup\{T=n\}
--   $$
-- source:
--   *Life Contingencies*, Chapter 2 §2.4.3, https://openacttextdev.github.io/LifeCon/C-ModelingLifeTimes.html; mathematical reconciliation of §3.2.3 eq (3.9) and §3.2.4 eq (3.10), https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib
import Definitions.Def_actuarial_strictSurvivalEvent
import Definitions.Def_actuarial_curtateSurvivalEvent
open MeasureTheory

namespace ActuarialValuation

theorem exact_curtate_survival_gap {Ω : Type*} (T : Ω → ℝ) (K : Ω → ℕ) (n : ℕ)
    (hKT : ∀ ω, (K ω : ℝ) ≤ T ω ∧ T ω < (K ω : ℝ) + 1)
    : (strictSurvivalEvent T n) ∪ {ω | T ω = (n : ℝ)} = (curtateSurvivalEvent K n) := by sorry

end ActuarialValuation
