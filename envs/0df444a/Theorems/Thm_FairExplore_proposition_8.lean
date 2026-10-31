-- Prove2me | Theorems.Thm_FairExplore_proposition_8
-- name    : FairExplore.proposition_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:15:41.796647+00:00
-- url     : https://prove2.me/theorems/6e12f42c-f415-4538-8677-2d6fb3b61886
-- title:
--   Proposition 8, p.34 — log-consistent policies: $\Pr(N_t(a)\le(1-\varepsilon)\log t/\mathrm{KL}\mid W^g_t)=O(1/\log t)$ (corrected: $p_g>0$)
-- statement:
--   Let $\mathcal I$ be a grouped $K$-armed bandit instance with parameter $\theta\in(0,1)^K$ (distinct entries) and let $\pi$ be a log-consistent policy (Definition 2; admissible and measurable). Let $g$ be a group, $a\in\mathcal A^g_{\mathrm{sub}}$ a suboptimal arm for $g$, and fix $\varepsilon\in(0,1)$. Let $\mathrm{Arr}^g_t=\sum_{s=1}^t\mathbf 1(g_s=g)$ and $W^g_t=\{\mathrm{Arr}^g_t\ge p_g t/2\}$. Then, as $t\to\infty$,
--   $$\Pr\Big(N_t(a)\le\frac{(1-\varepsilon)\log t}{\mathrm{KL}(\theta(a),\mathrm{OPT}(g))}\ \Big|\ W^g_t\Big)=O\Big(\frac1{\log t}\Big).$$
--
--   A probabilistic version of the Lai–Robbins bound; it is the main tool for Lemma 4 and Proposition 2.
--
--   **Formalization Note** $N_t(a)$ counts the pulls before time $t$; the conditional probability is $\Pr(E\cap W^g_t)/\Pr(W^g_t)$. The printed upper limit "$\sum_{s=1}^g$" of $\mathrm{Arr}^g_t$ is read as $\sum_{s=1}^t$.
--
--   Differences from the source:
--   - correction: p_g ≥ 0 with Σ_g p_g = 1 (p.6) → ∀ g, 0 < p g; reason: with p = (1, 0), A^1 = {2}, A^2 = {1, 2}, θ = (0.3, 0.6), g = 2, a = 1: the log-consistent policy that always pulls arm 2 has N_t(1) = 0 on every path and W^2_t is the sure event, so the conditional probability is 1, not O(1/log t); the proofs use p_g > 0 throughout (W^g_t, p.34; Claim 3, p.44; p.61)
--   - encoding: any policy → any admissible, measurable policy; reason: a policy of the model pulls an available arm (p.6), and expectations of the run presuppose measurability
--   - reading: consistency / log-consistency over every instance of the class → over every θ ∈ (0,1)^K with distinct entries, the structure (G, p, A^g) fixed; reason: the policy knows every quantity except θ (p.6), so the class it is designed for varies θ
--   - reading: Arr^g_t = Σ_{s=1}^g 1(g_t = g) → Arr^g_t = Σ_{s=1}^t 1(g_s = g); reason: the printed limits are a typo; the text says "the number of arrivals of group g by time t"
--   - encoding: A = [K], G a finite set → any finite linearly ordered arm type and any finite group type with the discrete σ-algebra; reason: every finite set of arms is order-isomorphic to [K]; the order is only used to index the uniform choice in step 1 of PF-UCB
--   - encoding: O(h(T)) as T → ∞, constants depending on the instance and the fixed parameters → ∃ C T₀, ∀ T ≥ T₀, … ≤ C · h(T), with C, T₀ chosen after the instance and the fixed parameters; reason: App. B.1, p.31
--   - encoding: times t = 1, 2, …; Pr and E → Lean step s is paper time s + 1; probabilities are measures of events, expectations are ∫⁻ of nonnegative quantities; reason: Lean indexing; same values
-- source:
--   Baek & Farias, Fair Exploration via Axiomatic Bargaining, arXiv:2106.02553v2, Proposition 8, (20), p.34 (proof §D.3); W^g_t and Arr^g_t, p.34

import Mathlib
import Definitions.Def_FairExplore_KArmed

open MeasureTheory

namespace FairExplore

/-- Proposition 8: for a log-consistent policy, a group `g`, an arm `a ∈ A^g_sub` and
`ε ∈ (0,1)`, `Pr(N_t(a) ≤ (1 − ε) log t / KL(θ(a), OPT(g)) | W^g_t) = O(1/log t)` as `t → ∞`, where
`W^g_t = {Arr^g_t ≥ p_g t/2}`. Baek & Farias, *Fair Exploration via Axiomatic Bargaining*, arXiv:2106.02553v2, Proposition 8, p.34 (proof §D.3).

**Formalization Note** Paper time `t = s + 1`: `N π ω s a` is `N_t(a)` (pulls before time `t`) and
`arrivals ω (s + 1) g` is `Arr^g_t = ∑_{u=1}^t 1(g_u = g)` (the printed upper limit `g` is a typo
for `t`). The conditional probability is `Pr(E ∩ W)/Pr(W)`. `O(1/log t)` is
`∃ C T₀, ∀ s ≥ T₀, … ≤ C / log t`. -/
theorem proposition_8 {γ α : Type*} [Fintype γ] [MeasurableSpace γ] [DiscreteMeasurableSpace γ] [DecidableEq γ]
    [Fintype α] [DecidableEq α]
    (S : GroupedStructure γ α) (hp : ∀ g, 0 < S.p g)
    (π : Policy γ α) (hπA : IsAdmissible S.A π) (hπM : IsMeasurablePolicy π) (hπ : IsLogConsistent S π)
    (θ : α → ℝ) (hθ : InKClass θ) (g : γ) (a : α) (ha : a ∈ subG S.A θ g)
    (ε : ℝ) (hε : ε ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ C T₀ : ℝ, ∀ s : ℕ, T₀ ≤ s →
      (law S (gaussLaw θ) ({ω | (N π ω s a : ℝ)
              ≤ (1 - ε) * Real.log ((s : ℝ) + 1) / klGauss (θ a) (opt S.A θ g)} ∩
            {ω | S.p g * ((s : ℝ) + 1) / 2 ≤ (arrivals ω (s + 1) g : ℝ)}) /
          law S (gaussLaw θ) {ω | S.p g * ((s : ℝ) + 1) / 2 ≤ (arrivals ω (s + 1) g : ℝ)}).toReal
        ≤ C / Real.log ((s : ℝ) + 1) := by sorry

end FairExplore
