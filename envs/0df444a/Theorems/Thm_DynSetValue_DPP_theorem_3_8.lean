-- Prove2me | Theorems.Thm_DynSetValue_DPP_theorem_3_8
-- name    : DynSetValue.DPP.theorem_3_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:21:32.104878+00:00
-- url     : https://prove2.me/theorems/75727774-2181-450c-87b2-988f344145e6
-- title:
--   Theorem 3.8 — stopping-time measurability of set membership
-- statement:
--   Under Assumptions 3.1 and 3.6(i), let $\tau$ be any $\mathcal F$-stopping time in $[0,T]$ and let $\eta$ be an $\mathcal F_\tau$-measurable $\mathbb R^N$-valued random vector. For every $\varepsilon>0$, both events
--
--   $$
--   \{\eta\in\widehat{\mathbb V}_\varepsilon(\tau,\cdot)\}
--   \quad\text{and}\quad
--   \{\eta\in\mathbb V(\tau,\cdot)\}
--   $$
--
--   belong to $\mathcal F_\tau$. This makes the dynamic principle's exceptional-event probability a measurable random-set condition.
-- source:
--   Feinstein, Rudloff, Zhang, Dynamic set values for nonzero sum games with multiple equilibriums, arXiv:2002.00449v2, p. 27, Theorem 3.8

import Mathlib
import Definitions.Def_DynSetValue_DPP_SetValue

open MeasureTheory
open scoped ENNReal NNReal Topology BigOperators

namespace DynSetValue.DPP

/-- Theorem 3.8, p. 27. -/
theorem theorem_3_8 {T : ℝ} (hT : 0 < T) {d N : ℕ}
    (G : Game T hT d N) (P0 : Measure (Ω T d))
    (hP0 : IsWiener hT P0) (h31 : Assumption31 G P0)
    (h36i : Assumption36i G)
    (ε : ℝ) (hε : 0 < ε)
    (τ : Ω T d → WithTop ℝ) (hτ : IsStoppingTime (𝓕 hT P0) τ)
    (hτrange : ∀ ω, (0 : WithTop ℝ) ≤ τ ω ∧ τ ω ≤ (T : WithTop ℝ))
    (η : Ω T d → Payoff N) (hη : Measurable[hτ.measurableSpace] η) :
    MeasurableSet[hτ.measurableSpace]
      {ω : Ω T d | η ω ∈ Vhat hT G P0 (stopTime τ ω) ω ε} ∧
    MeasurableSet[hτ.measurableSpace]
      {ω : Ω T d | η ω ∈ V hT G P0 (stopTime τ ω) ω} := by sorry

end DynSetValue.DPP
