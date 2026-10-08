-- Prove2me | Theorems.Thm_BertsekasShreve_BorelFinite_lemma8_2_eps_selector
-- name    : BertsekasShreve.BorelFinite.lemma8_2_eps_selector
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T04:17:42.063747+00:00
-- url     : https://prove2.me/theorems/2068fc3b-6de9-487f-8891-f4dc0c93ae13
-- title:
--   Lemma 8.2 — a universally measurable kernel μ with T_μ(J) ≤ T(J) + ε
-- statement:
--   Consider the finite horizon Borel model of Definition 8.1. Let $J:S\to R^*$ be lower semianalytic. Then for every $\varepsilon>0$ there exists $\mu\in U(C\mid S)$ such that
--   $$T_\mu(J)(x)\le T(J)(x)+\varepsilon\qquad\forall x\in S,$$
--   where $T(J)(x)+\varepsilon$ may be $-\infty$.
--
--   The lemma is the measurable-selection step of the dynamic programming algorithm: one step of $T$ can be nearly attained by a single universally measurable randomized control law, uniformly in the state, including where the infimum is $-\infty$.
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, p. 196, Lemma 8.2

import Mathlib
import Definitions.Def_BertsekasShreve_BorelFinite_Model
import Definitions.Def_BertsekasShreve_BorelFinite_Policy
import Definitions.Def_BertsekasShreve_BorelFinite_Operators

namespace BertsekasShreve.BorelFinite

/-- **Lemma 8.2** (p. 196). If `J : S → R*` is lower semianalytic, then for `ε > 0` there exists
`μ ∈ U(C|S)` with `T_μ(J)(x) ≤ T(J)(x) + ε` for all `x ∈ S` (the right side may be `-∞`). -/
theorem lemma8_2_eps_selector {S C W : Type*}
    [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S] [BertsekasShreve.AnalyticSelection.IsBorelSpace S] [Nonempty S]
    [TopologicalSpace C] [MeasurableSpace C] [BorelSpace C] [BertsekasShreve.AnalyticSelection.IsBorelSpace C] [Nonempty C]
    [TopologicalSpace W] [MeasurableSpace W] [BorelSpace W] [BertsekasShreve.AnalyticSelection.IsBorelSpace W] [Nonempty W]
    (M : Model S C W)
    (J : S → EReal) (hJ : IsLowerSemianalyticOn Set.univ J) (ε : ℝ) (hε : 0 < ε) :
    ∃ μ : UCS M, ∀ x : S, Tmu M μ J x ≤ T M J x + (ε : EReal) := by sorry

end BertsekasShreve.BorelFinite
