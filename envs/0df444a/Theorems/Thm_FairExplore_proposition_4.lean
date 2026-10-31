-- Prove2me | Theorems.Thm_FairExplore_proposition_4
-- name    : FairExplore.proposition_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:18:22.220098+00:00
-- url     : https://prove2.me/theorems/15073ab7-73fa-42ba-a8b4-a452898e8746
-- title:
--   Proposition 4, p.16 — PF-UCB: non-greedy pulls of a suboptimal arm off $H_t(\delta)$ occur $O(\log\log T)$ times
-- statement:
--   Let $\mathcal I$ be a grouped $K$-armed bandit instance with parameter $\theta\in(0,1)^K$ (distinct entries), and run PF-UCB. Fix any $\delta>0$ and let $H_t(\delta)$ be the event $\hat\theta_t(b)\in[\theta(b)-\delta,\theta(b)+\delta]$ for all arms $b$. For any group $g$ and arm $a\in\mathcal A^g_{\mathrm{sub}}$ suboptimal for $g$,
--   $$\sum_{t=1}^T\Pr\big(\mathrm{Pull}^g_t(a),\ A^{\mathrm{greedy}}_t(g)\neq a,\ \bar H_t(\delta)\big)=O(\log\log T),$$
--   the constant depending on $\delta$ and the instance.
--
--   Together with Proposition 3 this shows that, apart from $O(\log\log T)$ pulls, PF-UCB follows $q^*$.
--
--   Differences from the source:
--   - reading: p_g ≥ 0 with Σ_g p_g = 1 (p.6) → ∀ g, 0 < p g; reason: §2.1 does not say whether a group may have p_g = 0; the paper results about this model (Theorem 3, Theorem 9, Propositions 1, 2, 8–11, Lemmas 4 and 9) are false at p_g = 0 (counterexamples in those items), so p_g > 0 is read as a standing assumption of the model, as every proof of App. C–E uses it (W^g_t, p.34; Claim 3, p.44); no counterexample to this item at p_g = 0 is known
--   - encoding: A^g unrestricted → every A^g nonempty; reason: OPT(g) = max over A^g and the pull A_t ∈ A^{g_t} are undefined otherwise
--   - encoding: G_a unrestricted → every arm belongs to some group; reason: J(a) = max over G_a is undefined otherwise and (13) is infeasible (Σ_g q^g(a) = 1 with every q^g(a) = 0)
--   - reading: UCB_t(a) = max{q : N_t(a)KL(θ̂_t(a), q) ≤ log t + 3 log log t}, θ̂_t empirical mean → f(1) = f(2) = f(3) = log 3 + 3 log log 3, UCB = +∞ and θ̂ = 0 for an unpulled arm; reason: log log t is undefined at t = 1 and negative at t = 2, and θ̂ of an unpulled arm is undefined; the convention is that of the published CappeKLUCB_ExpFam_Setting, and the result is asymptotic
--   - generalization: PF-UCB with an unspecified choice in each "∈ arg max" → PF-UCB with every tie-breaking rule sel; reason: a statement for every rule specializes to the paper policy whatever choice it makes
--   - encoding: A = [K], G a finite set → any finite linearly ordered arm type and any finite group type with the discrete σ-algebra; reason: every finite set of arms is order-isomorphic to [K]; the order is only used to index the uniform choice in step 1 of PF-UCB
--   - encoding: times t = 1, 2, …; Pr and E → Lean step s is paper time s + 1; probabilities are measures of events, expectations are ∫⁻ of nonnegative quantities; reason: Lean indexing; same values
--   - encoding: O(h(T)) as T → ∞, constants depending on the instance and the fixed parameters → ∃ C T₀, ∀ T ≥ T₀, … ≤ C · h(T), with C, T₀ chosen after the instance and the fixed parameters; reason: App. B.1, p.31
-- source:
--   Baek & Farias, Fair Exploration via Axiomatic Bargaining, arXiv:2106.02553v2, Proposition 4, p.16 (proof pp.42–43); H_t(δ), p.15

import Mathlib
import Definitions.Def_FairExplore_Policies

open MeasureTheory

namespace FairExplore

/-- Proposition 4: under PF-UCB, fix any `δ > 0`. For any group `g` and arm `a ∈ A^g_sub`,
`∑_{t=1}^T Pr(Pull^g_t(a), A^greedy_t(g) ≠ a, H̄_t(δ)) = O(log log T)`, where
`H_t(δ) = 1(θ̂_t(a) ∈ [θ(a) − δ, θ(a) + δ] ∀ a ∈ A)`.
Baek & Farias, *Fair Exploration via Axiomatic Bargaining*, arXiv:2106.02553v2, Proposition 4, p.16 (proof pp.42–43); `H_t(δ)` p.15.

**Formalization Note** `θ̂_t` is the empirical mean before the pull (`0` for an unpulled arm). The
constant may depend on `δ`. Step `s` is paper time `s + 1`. -/
theorem proposition_4 {γ α : Type*} [Fintype γ] [MeasurableSpace γ] [DiscreteMeasurableSpace γ] [DecidableEq γ]
    [Fintype α] [LinearOrder α]
    (S : GroupedStructure γ α) (hp : ∀ g, 0 < S.p g) (hA : ∀ g, (S.A g).Nonempty)
    (hG : ∀ a, ∃ g, a ∈ S.A g) (θ : α → ℝ) (hθ : InKClass θ)
    (sel : Finset α → α) (hsel : IsSelector sel)
    (δ : ℝ) (hδ : 0 < δ) (g : γ) (a : α) (ha : a ∈ subG S.A θ g) :
    ∃ C T₀ : ℝ, ∀ T : ℕ, T₀ ≤ T →
      ∑ s ∈ Finset.range T,
          (law S (gaussLaw θ) {ω | ω.1 s = g ∧ arm (pfucb S.A sel) ω s = a ∧
              (hist (pfucb S.A sel) ω s).greedy sel S.A g ≠ a ∧
              ¬ ∀ b, (hist (pfucb S.A sel) ω s).mean b ∈ Set.Icc (θ b - δ) (θ b + δ)}).toReal
        ≤ C * Real.log (Real.log T) := by sorry

end FairExplore
