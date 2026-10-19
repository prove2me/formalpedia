-- Prove2me | Theorems.Thm_DynSetValue_DPP_theorem_3_9
-- name    : DynSetValue.DPP.theorem_3_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:21:24.169231+00:00
-- url     : https://prove2.me/theorems/dd1aa079-b4ae-473f-9baa-6b9f0da1590e
-- title:
--   Theorem 3.9 — dynamic programming principle for the set value
-- statement:
--   Under Assumptions 3.1 and 3.6, fix any $\mathcal F$-stopping time $\tau\in[0,T]$ with $\tau(0)>0$. At the zero history and initial time, the full-horizon set value equals the intersection, over $\varepsilon>0$, of stopped-game costs within an open $\varepsilon$-ball for which there exist a bounded $\mathcal F_\tau$-measurable terminal payoff $\eta$ and an $\varepsilon$-equilibrium $\alpha$ satisfying
--
--   $$
--   \mathbb P_0\!\left(\eta\notin\widehat{\mathbb V}_\varepsilon(\tau,B)\right)\le\varepsilon.
--   $$
--
--   Equivalently, this is equation (3.12) of the source. The same $\varepsilon$ appears in the approximate equilibrium, value ball and exceptional-event bound.
--
--   **Formalization Note** The goal uses the $t=0$ form treated in the paper's proof. At a general fixed history, concatenation can map Wiener paths into a null set where the augmented filtration does not constrain an arbitrary stopped payoff. The set-builder phrase “for all $\eta$ and $\alpha$” is interpreted existentially, as its proof uses it.
-- source:
--   Feinstein, Rudloff, Zhang, Dynamic set values for nonzero sum games with multiple equilibriums, arXiv:2002.00449v2, p. 28, Theorem 3.9, in the form (3.12), p. 29

import Mathlib
import Definitions.Def_DynSetValue_DPP_SetValue

open MeasureTheory
open scoped ENNReal NNReal Topology BigOperators

namespace DynSetValue.DPP

/-- Theorem 3.9 in the proved form (3.12), p. 29. -/
theorem theorem_3_9 {T : ℝ} (hT : 0 < T) {d N : ℕ}
    (G : Game T hT d N) (P0 : Measure (Ω T d))
    (hP0 : IsWiener hT P0) (h31 : Assumption31 G P0)
    (h36i : Assumption36i G) (h36ii : Assumption36ii G)
    (τ : Ω T d → WithTop ℝ) (hτ : IsStoppingTime (𝓕 hT P0) τ)
    (hτrange : ∀ ω, (0 : WithTop ℝ) ≤ τ ω ∧ τ ω ≤ (T : WithTop ℝ))
    (hτzero : (0 : WithTop ℝ) < τ (zeroPath T d)) :
    V hT G P0 0 (zeroPath T d) =
      ⋂ ε > 0, {y : Payoff N |
        ∃ (η : Ω T d → Payoff N) (α : Profile hT G),
          Measurable[hτ.measurableSpace] η ∧
          (∃ C : ℝ, ∀ ω, ‖η ω‖ ≤ C) ∧
          NEεStop hT G P0 τ η 0 (zeroPath T d) ε α ∧
          y ∈ Metric.ball (Jstop hT G P0 τ η 0 (zeroPath T d) α) ε ∧
          P0 {ω : Ω T d | η ω ∉ Vhat hT G P0 (stopTime τ ω) ω ε} ≤
            ENNReal.ofReal ε} := by sorry

end DynSetValue.DPP
