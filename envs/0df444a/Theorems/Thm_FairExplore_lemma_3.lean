-- Prove2me | Theorems.Thm_FairExplore_lemma_3
-- name    : FairExplore.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:15:26.997099+00:00
-- url     : https://prove2.me/theorems/ccb3af7c-21f4-45cb-91ab-31a28b0d7669
-- title:
--   Lemma 3, p.32 — a pulled arm's empirical mean leaves $[L,U]$ only $O(1)$ times
-- statement:
--   Consider a grouped $K$-armed bandit with parameter $\theta\in(0,1)^K$ (distinct entries) and any admissible measurable policy. Let $g$ be a group, $a\in\mathcal A^g$ an arm and $L<\theta(a)<U$. Then
--   $$\sum_{t=1}^T\Pr\big(\mathrm{Pull}_t(a),\ \hat\theta_t(a)\notin[L,U]\big)=O(1),$$
--   where $\mathrm{Pull}_t(a)$ is the event that arm $a$ is pulled at time $t$, $\hat\theta_t(a)$ is its empirical mean before that pull, and the constant depends on the instance and on $L,U$.
--
--   Differences from the source:
--   - encoding: any policy → any admissible, measurable policy; reason: a policy of the model pulls an available arm (p.6), and expectations of the run presuppose measurability
--   - reading: θ̂_t(a) of an arm that has not been pulled → 0; reason: the paper leaves it undefined; it is the mean of zero observations
--   - encoding: A = [K], G a finite set → any finite linearly ordered arm type and any finite group type with the discrete σ-algebra; reason: every finite set of arms is order-isomorphic to [K]; the order is only used to index the uniform choice in step 1 of PF-UCB
--   - encoding: O(h(T)) as T → ∞, constants depending on the instance and the fixed parameters → ∃ C T₀, ∀ T ≥ T₀, … ≤ C · h(T), with C, T₀ chosen after the instance and the fixed parameters; reason: App. B.1, p.31
--   - encoding: times t = 1, 2, …; Pr and E → Lean step s is paper time s + 1; probabilities are measures of events, expectations are ∫⁻ of nonnegative quantities; reason: Lean indexing; same values
-- source:
--   Baek & Farias, Fair Exploration via Axiomatic Bargaining, arXiv:2106.02553v2, Lemma 3, pp.32–33

import Mathlib
import Definitions.Def_FairExplore_KArmed

open MeasureTheory

namespace FairExplore

/-- Lemma 3: for any group `g`, arm `a ∈ A^g` and `L < θ(a) < U`,
`∑_{t=1}^T Pr(Pull_t(a), θ̂_t(a) ∉ [L, U]) = O(1)`, the constant depending on the instance and
`L, U`. Baek & Farias, *Fair Exploration via Axiomatic Bargaining*, arXiv:2106.02553v2, Lemma 3, pp.32–33.

**Formalization Note** Step `s` is paper time `s + 1`; `θ̂_t(a)` is the empirical mean before the
pull. `O(1)` is `∃ C T₀, ∀ T ≥ T₀, … ≤ C`. Any admissible measurable policy. -/
theorem lemma_3 {γ α : Type*} [Fintype γ] [MeasurableSpace γ] [DiscreteMeasurableSpace γ] [DecidableEq γ]
    [Fintype α] [DecidableEq α]
    (S : GroupedStructure γ α) (θ : α → ℝ) (hθ : InKClass θ)
    (π : Policy γ α) (hπA : IsAdmissible S.A π) (hπM : IsMeasurablePolicy π)
    (g : γ) (a : α) (ha : a ∈ S.A g) (L U : ℝ) (hL : L < θ a) (hU : θ a < U) :
    ∃ C T₀ : ℝ, ∀ T : ℕ, T₀ ≤ T →
      ∑ s ∈ Finset.range T,
          (law S (gaussLaw θ) {ω | arm π ω s = a ∧ (hist π ω s).mean a ∉ Set.Icc L U}).toReal ≤ C := by sorry

end FairExplore
