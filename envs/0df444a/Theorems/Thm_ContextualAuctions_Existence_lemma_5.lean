-- Prove2me | Theorems.Thm_ContextualAuctions_Existence_lemma_5
-- name    : ContextualAuctions.Existence.lemma_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T19:30:14.118613+00:00
-- url     : https://prove2.me/theorems/074be818-4401-41ee-a3ab-908f73ac399c
-- title:
--   Lemma 5, p. 10 — a fixed point µ ∈ C*₀(µ) is a.s. dual optimal: µ(w,B) ∈ argmin_{t∈[0,ω/B_min]} q^µ(w,B,t)
-- statement:
--   Work in the contextual first price auction model with budgets (see the `Setting` and `FixedPoint` modules), under its standing assumptions. If $\mu\in\mathcal X_0$ and $\mu\in C^*_0(\mu)=\arg\min_{\hat\mu\in\mathcal X_0}f(\mu,\hat\mu)$, then $\mu(w,B)$ is almost surely optimal for each type:
--
--   $$
--   \mu(w,B)\in\arg\min_{t\in[0,\omega/B_{\min}]}q^\mu(w,B,t)\qquad\text{for $G$-almost every }(w,B).
--   $$
--
--   The combined problem over functions $\hat\mu$ thus solves the individual one-dimensional dual problems of almost every type.
--
--   **Formalization Note** Membership in the argmin is stated as $\mu(w,B)\in[0,\omega/B_{\min}]$ together with minimality over that interval.
-- source:
--   Balseiro, Kroer, Kumar, Contextual Standard Auctions with Budgets: Revenue Equivalence and Efficiency Guarantees, Management Science, Articles in Advance (2023), doi:10.1287/mnsc.2023.4719, p. 10, Lemma 5

import Mathlib
import Definitions.Def_ContextualAuctions_Existence_Setting
import Definitions.Def_ContextualAuctions_Existence_FixedPoint

namespace ContextualAuctions.Existence

open MeasureTheory

theorem lemma_5 (M : Model) (hM : M.Standing) (μ : (Fin M.d → ℝ) × ℝ → ℝ) (hμ : μ ∈ X0 M)
    (hfix : μ ∈ C0star M μ) :
    ∀ᵐ θ ∂M.G, μ θ ∈ Set.Icc 0 (omega M / M.Bmin) ∧
      IsMinOn (qDual M μ θ) (Set.Icc 0 (omega M / M.Bmin)) (μ θ) := by sorry

end ContextualAuctions.Existence
