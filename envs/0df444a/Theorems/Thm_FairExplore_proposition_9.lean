-- Prove2me | Theorems.Thm_FairExplore_proposition_9
-- name    : FairExplore.proposition_9
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:15:49.552456+00:00
-- url     : https://prove2.me/theorems/0188fce3-7e2c-4c9c-9bc9-851b66e2a123
-- title:
--   Proposition 9, p.34 — log-consistent policies pull an optimal arm more than $b\log t$ times w.h.p. (corrected: $p_g>0$)
-- statement:
--   Let $\mathcal I$ be a grouped $K$-armed bandit instance with parameter $\theta\in(0,1)^K$ (distinct entries) and let $\pi$ be a log-consistent policy (admissible and measurable). Let $a$ be an arm that is optimal for some group $g$ ($a\in\mathcal A^g$, $\theta(a)=\mathrm{OPT}(g)$). Then for any $b>0$, as $t\to\infty$,
--   $$\Pr\big(N_t(a)\le b\log t\ \big|\ W^g_t\big)=O\Big(\frac1{\log t}\Big),$$
--   the constants depending on $b$ and the instance, where $W^g_t=\{\mathrm{Arr}^g_t\ge p_gt/2\}$.
--
--   **Formalization Note** As in Proposition 8: $N_t(a)$ counts the pulls before time $t$ and the conditional probability is $\Pr(E\cap W^g_t)/\Pr(W^g_t)$.
--
--   Differences from the source:
--   - correction: p_g ≥ 0 with Σ_g p_g = 1 (p.6) → ∀ g, 0 < p g; reason: with p = (1, 0), A^1 = {1}, A^2 = {2}, θ = (0.3, 0.6), arm 2 is optimal for group 2, which never arrives; every admissible policy has N_t(2) = 0 and W^2_t is the sure event, so the conditional probability is 1, not O(1/log t); the proofs use p_g > 0 throughout (W^g_t, p.34; Claim 3, p.44; p.61)
--   - encoding: any policy → any admissible, measurable policy; reason: a policy of the model pulls an available arm (p.6), and expectations of the run presuppose measurability
--   - reading: consistency / log-consistency over every instance of the class → over every θ ∈ (0,1)^K with distinct entries, the structure (G, p, A^g) fixed; reason: the policy knows every quantity except θ (p.6), so the class it is designed for varies θ
--   - encoding: A = [K], G a finite set → any finite linearly ordered arm type and any finite group type with the discrete σ-algebra; reason: every finite set of arms is order-isomorphic to [K]; the order is only used to index the uniform choice in step 1 of PF-UCB
--   - encoding: O(h(T)) as T → ∞, constants depending on the instance and the fixed parameters → ∃ C T₀, ∀ T ≥ T₀, … ≤ C · h(T), with C, T₀ chosen after the instance and the fixed parameters; reason: App. B.1, p.31
--   - encoding: times t = 1, 2, …; Pr and E → Lean step s is paper time s + 1; probabilities are measures of events, expectations are ∫⁻ of nonnegative quantities; reason: Lean indexing; same values
-- source:
--   Baek & Farias, Fair Exploration via Axiomatic Bargaining, arXiv:2106.02553v2, Proposition 9, p.34

import Mathlib
import Definitions.Def_FairExplore_KArmed

open MeasureTheory

namespace FairExplore

/-- Proposition 9: for a log-consistent policy and an arm `a` optimal for some group `g`,
for any `b > 0`, `Pr(N_t(a) ≤ b log t | W^g_t) = O(1/log t)` as `t → ∞`, the constants depending on
`b` and the instance. Baek & Farias, *Fair Exploration via Axiomatic Bargaining*, arXiv:2106.02553v2, Proposition 9, p.34.

**Formalization Note** As in Proposition 8: paper time `t = s + 1`, `W^g_t = {Arr^g_t ≥ p_g t/2}`,
conditional probability `Pr(E ∩ W)/Pr(W)`. "Optimal for `g`" is `a ∈ A^g` and `θ(a) = OPT(g)`. -/
theorem proposition_9 {γ α : Type*} [Fintype γ] [MeasurableSpace γ] [DiscreteMeasurableSpace γ] [DecidableEq γ]
    [Fintype α] [DecidableEq α]
    (S : GroupedStructure γ α) (hp : ∀ g, 0 < S.p g)
    (π : Policy γ α) (hπA : IsAdmissible S.A π) (hπM : IsMeasurablePolicy π) (hπ : IsLogConsistent S π)
    (θ : α → ℝ) (hθ : InKClass θ) (g : γ) (a : α) (ha : a ∈ S.A g) (hopt : θ a = opt S.A θ g)
    (b : ℝ) (hb : 0 < b) :
    ∃ C T₀ : ℝ, ∀ s : ℕ, T₀ ≤ s →
      (law S (gaussLaw θ) ({ω | (N π ω s a : ℝ) ≤ b * Real.log ((s : ℝ) + 1)} ∩
            {ω | S.p g * ((s : ℝ) + 1) / 2 ≤ (arrivals ω (s + 1) g : ℝ)}) /
          law S (gaussLaw θ) {ω | S.p g * ((s : ℝ) + 1) / 2 ≤ (arrivals ω (s + 1) g : ℝ)}).toReal
        ≤ C / Real.log ((s : ℝ) + 1) := by sorry

end FairExplore
