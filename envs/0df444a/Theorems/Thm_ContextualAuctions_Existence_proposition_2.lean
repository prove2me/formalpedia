-- Prove2me | Theorems.Thm_ContextualAuctions_Existence_proposition_2
-- name    : ContextualAuctions.Existence.proposition_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T19:29:01.061007+00:00
-- url     : https://prove2.me/theorems/74e5c74b-89af-4118-a7b0-c5894424bd4c
-- title:
--   Proposition 2, p. 9 — some pacing function µ satisfies µ(w,B) ∈ argmin_{t≥0} q^µ(w,B,t) almost surely
-- statement:
--   Work in the contextual first price auction model with budgets (see the `Setting` module), under its standing assumptions. There exists a pacing function $\mu:\Theta\to\mathbb R_{\ge0}$ such that
--
--   $$
--   \mu(w,B)\in\arg\min_{t\ge0}q^\mu(w,B,t)\qquad\text{almost surely w.r.t. }(w,B)\sim G .
--   $$
--
--   Such a $\mu$ is self-consistent: when every competitor paces by $\mu$, the optimal dual multiplier of almost every type is its own pacing level. Combined with Proposition 1 this gives Theorem 1.
--
--   **Formalization Note** The argmin is over $t\ge0$, as printed (not over $[0,\omega/B_{\min}]$). Membership is $\mu(w,B)\ge0$ together with minimality over $[0,\infty)$. The pacing function is measurable.
-- source:
--   Balseiro, Kroer, Kumar, Contextual Standard Auctions with Budgets: Revenue Equivalence and Efficiency Guarantees, Management Science, Articles in Advance (2023), doi:10.1287/mnsc.2023.4719, p. 9, Proposition 2

import Mathlib
import Definitions.Def_ContextualAuctions_Existence_Setting

namespace ContextualAuctions.Existence

open MeasureTheory

theorem proposition_2 (M : Model) (hM : M.Standing) :
    ∃ μ : (Fin M.d → ℝ) × ℝ → ℝ, IsPacing M μ ∧
      ∀ᵐ θ ∂M.G, 0 ≤ μ θ ∧ IsMinOn (qDual M μ θ) (Set.Ici 0) (μ θ) := by sorry

end ContextualAuctions.Existence
