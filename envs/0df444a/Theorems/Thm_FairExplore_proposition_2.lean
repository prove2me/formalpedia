-- Prove2me | Theorems.Thm_FairExplore_proposition_2
-- name    : FairExplore.proposition_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:18:15.432438+00:00
-- url     : https://prove2.me/theorems/86c4ee32-d4b7-47c8-9efb-17cae3b49998
-- title:
--   Proposition 2, p.15 — PF-UCB: greedy pulls of a suboptimal arm occur $O(\log\log T)$ times (corrected: $p_g>0$)
-- statement:
--   Let $\mathcal I$ be a grouped $K$-armed bandit instance with parameter $\theta\in(0,1)^K$ (distinct entries), and run PF-UCB. For any group $g$ and arm $a\in\mathcal A^g_{\mathrm{sub}}$ suboptimal for $g$,
--   $$\sum_{t=1}^T\Pr\big(\mathrm{Pull}^g_t(a),\ A^{\mathrm{greedy}}_t(g)=a\big)=O(\log\log T),$$
--   where $\mathrm{Pull}^g_t(a)=\mathbf 1(g_t=g,A_t=a)$ and $A^{\mathrm{greedy}}_t(g)\in\arg\max_{a\in\mathcal A^g}\hat\theta_t(a)$.
--
--   So the regret of PF-UCB comes from pulls of arms with the highest UCB for some group.
--
--   **Formalization Note** The greedy arm uses the same tie-breaking rule as PF-UCB.
--
--   Differences from the source:
--   - correction: p_g ≥ 0 with Σ_g p_g = 1 (p.6) → ∀ g, 0 < p g; reason: with p = (1, 0), A^1 = A^2 = {1, 2}, θ = (0.3, 0.6), the program P(θ̂) is symmetric in the two groups, so q̂^1_t(a) ≤ 1/2 for each arm once both arms have been pulled; step 1 then fires only for the first pull of each arm and PF-UCB is greedy afterwards; with positive probability the single sample of arm 2 lies below every running mean of arm 1, and group 1 then pulls the suboptimal arm 1 greedily at every later step, so the sum grows linearly in T; the proofs use p_g > 0 throughout (W^g_t, p.34; Claim 3, p.44; p.61)
--   - encoding: A^g unrestricted → every A^g nonempty; reason: OPT(g) = max over A^g and the pull A_t ∈ A^{g_t} are undefined otherwise
--   - encoding: G_a unrestricted → every arm belongs to some group; reason: J(a) = max over G_a is undefined otherwise and (13) is infeasible (Σ_g q^g(a) = 1 with every q^g(a) = 0)
--   - reading: UCB_t(a) = max{q : N_t(a)KL(θ̂_t(a), q) ≤ log t + 3 log log t}, θ̂_t empirical mean → f(1) = f(2) = f(3) = log 3 + 3 log log 3, UCB = +∞ and θ̂ = 0 for an unpulled arm; reason: log log t is undefined at t = 1 and negative at t = 2, and θ̂ of an unpulled arm is undefined; the convention is that of the published CappeKLUCB_ExpFam_Setting, and the result is asymptotic
--   - generalization: PF-UCB with an unspecified choice in each "∈ arg max" → PF-UCB with every tie-breaking rule sel; reason: a statement for every rule specializes to the paper policy whatever choice it makes
--   - encoding: A = [K], G a finite set → any finite linearly ordered arm type and any finite group type with the discrete σ-algebra; reason: every finite set of arms is order-isomorphic to [K]; the order is only used to index the uniform choice in step 1 of PF-UCB
--   - encoding: times t = 1, 2, …; Pr and E → Lean step s is paper time s + 1; probabilities are measures of events, expectations are ∫⁻ of nonnegative quantities; reason: Lean indexing; same values
--   - encoding: O(h(T)) as T → ∞, constants depending on the instance and the fixed parameters → ∃ C T₀, ∀ T ≥ T₀, … ≤ C · h(T), with C, T₀ chosen after the instance and the fixed parameters; reason: App. B.1, p.31
-- source:
--   Baek & Farias, Fair Exploration via Axiomatic Bargaining, arXiv:2106.02553v2, Proposition 2, p.15 (proof pp.41–42)

import Mathlib
import Definitions.Def_FairExplore_Policies

open MeasureTheory

namespace FairExplore

/-- Proposition 2: under PF-UCB, for any group `g` and arm `a ∈ A^g_sub`,
`∑_{t=1}^T Pr(Pull^g_t(a), A^greedy_t(g) = a) = O(log log T)`.
Baek & Farias, *Fair Exploration via Axiomatic Bargaining*, arXiv:2106.02553v2, Proposition 2, p.15 (proof pp.41–42).

**Formalization Note** `Pull^g_t(a) = 1(g_t = g, A_t = a)`; the greedy arm is computed from the
history before the pull, with ties broken by the same selector `sel` as PF-UCB. Step `s` is paper
time `s + 1`. -/
theorem proposition_2 {γ α : Type*} [Fintype γ] [MeasurableSpace γ] [DiscreteMeasurableSpace γ] [DecidableEq γ]
    [Fintype α] [LinearOrder α]
    (S : GroupedStructure γ α) (hp : ∀ g, 0 < S.p g) (hA : ∀ g, (S.A g).Nonempty)
    (hG : ∀ a, ∃ g, a ∈ S.A g) (θ : α → ℝ) (hθ : InKClass θ)
    (sel : Finset α → α) (hsel : IsSelector sel)
    (g : γ) (a : α) (ha : a ∈ subG S.A θ g) :
    ∃ C T₀ : ℝ, ∀ T : ℕ, T₀ ≤ T →
      ∑ s ∈ Finset.range T,
          (law S (gaussLaw θ) {ω | ω.1 s = g ∧ arm (pfucb S.A sel) ω s = a ∧
              (hist (pfucb S.A sel) ω s).greedy sel S.A g = a}).toReal
        ≤ C * Real.log (Real.log T) := by sorry

end FairExplore
