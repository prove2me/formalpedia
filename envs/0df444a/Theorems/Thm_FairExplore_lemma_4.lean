-- Prove2me | Theorems.Thm_FairExplore_lemma_4
-- name    : FairExplore.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:15:50.225337+00:00
-- url     : https://prove2.me/theorems/7371e151-009d-499e-b259-bb8315a08351
-- title:
--   Lemma 4, p.34 — log-consistent policies rarely pull $a$ while $\mathrm{UCB}_t(a)\ge\mathrm{OPT}(\Gamma(a))+r$ (corrected: $p_g>0$)
-- statement:
--   Let $\mathcal I$ be a grouped $K$-armed bandit instance with parameter $\theta\in(0,1)^K$ (distinct entries) and run any log-consistent policy $\pi$ (admissible and measurable). Fix $r>0$. For any arm $a$ (connected to at least one group),
--   $$\sum_{t=1}^T\Pr\big(\mathrm{Pull}_t(a),\ \mathrm{UCB}_t(a)\ge\mathrm{OPT}(\Gamma(a))+r\big)=O(\log\log T),$$
--   where $\mathrm{OPT}(\Gamma(a))=\min_{g\in G_a}\mathrm{OPT}(g)$ and the constant may depend on the instance and $r$.
--
--   Differences from the source:
--   - correction: p_g ≥ 0 with Σ_g p_g = 1 (p.6) → ∀ g, 0 < p g; reason: with p = (1, 0), A^1 = {1, 2}, A^2 = {1}, θ = (0.3, 0.6), OPT(Γ(1)) = θ(1); the log-consistent policy that lets group 1 pull arm 1 whenever N_t(1) < r^(-2) log t and otherwise follows KL-UCB pulls arm 1 about r^(-2) log T times with UCB_t(1) ≥ θ̂_t(1) + √2 r, so the sum grows like log T, not O(log log T); the proofs use p_g > 0 throughout (W^g_t, p.34; Claim 3, p.44; p.61)
--   - encoding: any a ∈ A → any arm with G_a nonempty; reason: Γ(a) = argmin over G_a is undefined otherwise
--   - encoding: any policy → any admissible, measurable policy; reason: a policy of the model pulls an available arm (p.6), and expectations of the run presuppose measurability
--   - reading: consistency / log-consistency over every instance of the class → over every θ ∈ (0,1)^K with distinct entries, the structure (G, p, A^g) fixed; reason: the policy knows every quantity except θ (p.6), so the class it is designed for varies θ
--   - reading: UCB_t(a) = max{q : N_t(a)KL(θ̂_t(a), q) ≤ log t + 3 log log t}, θ̂_t empirical mean → f(1) = f(2) = f(3) = log 3 + 3 log log 3, UCB = +∞ and θ̂ = 0 for an unpulled arm; reason: log log t is undefined at t = 1 and negative at t = 2, and θ̂ of an unpulled arm is undefined; the convention is that of the published CappeKLUCB_ExpFam_Setting, and the result is asymptotic
--   - encoding: A = [K], G a finite set → any finite linearly ordered arm type and any finite group type with the discrete σ-algebra; reason: every finite set of arms is order-isomorphic to [K]; the order is only used to index the uniform choice in step 1 of PF-UCB
--   - encoding: O(h(T)) as T → ∞, constants depending on the instance and the fixed parameters → ∃ C T₀, ∀ T ≥ T₀, … ≤ C · h(T), with C, T₀ chosen after the instance and the fixed parameters; reason: App. B.1, p.31
--   - encoding: times t = 1, 2, …; Pr and E → Lean step s is paper time s + 1; probabilities are measures of events, expectations are ∫⁻ of nonnegative quantities; reason: Lean indexing; same values
-- source:
--   Baek & Farias, Fair Exploration via Axiomatic Bargaining, arXiv:2106.02553v2, Lemma 4, p.34

import Mathlib
import Definitions.Def_FairExplore_KArmed

open MeasureTheory

namespace FairExplore

/-- Lemma 4: for any log-consistent policy, fixed `r > 0` and any arm `a`,
`∑_{t=1}^T Pr(Pull_t(a), UCB_t(a) ≥ OPT(Γ(a)) + r) = O(log log T)`, the constant depending on the
instance and `r`. Baek & Farias, *Fair Exploration via Axiomatic Bargaining*, arXiv:2106.02553v2, Lemma 4, p.34.

**Formalization Note** `OPT(Γ(a)) = min_{g ∈ G_a} OPT(g)` (`optGamma`); the arm belongs to some
group, so `G_a ≠ ∅` and `Γ(a)` is defined. Step `s` is paper time `s + 1`. -/
theorem lemma_4 {γ α : Type*} [Fintype γ] [MeasurableSpace γ] [DiscreteMeasurableSpace γ] [DecidableEq γ]
    [Fintype α] [DecidableEq α]
    (S : GroupedStructure γ α) (hp : ∀ g, 0 < S.p g)
    (π : Policy γ α) (hπA : IsAdmissible S.A π) (hπM : IsMeasurablePolicy π) (hπ : IsLogConsistent S π)
    (θ : α → ℝ) (hθ : InKClass θ) (r : ℝ) (hr : 0 < r) (a : α) (ha : ∃ g, a ∈ S.A g) :
    ∃ C T₀ : ℝ, ∀ T : ℕ, T₀ ≤ T →
      ∑ s ∈ Finset.range T,
          (law S (gaussLaw θ) {ω | arm π ω s = a ∧
              (((optGamma S.A θ a + r : ℝ)) : EReal) ≤ (hist π ω s).ucb a}).toReal
        ≤ C * Real.log (Real.log T) := by sorry

end FairExplore
