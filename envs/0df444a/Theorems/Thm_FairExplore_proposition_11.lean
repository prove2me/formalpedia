-- Prove2me | Theorems.Thm_FairExplore_proposition_11
-- name    : FairExplore.proposition_11
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:18:18.893187+00:00
-- url     : https://prove2.me/theorems/45a6ea14-78e9-4f0d-9e48-a200e31b5f53
-- title:
--   Proposition 11, p.40 — PF-UCB pulls each $a\in\mathcal A_{\mathrm{sub}}$ $J(a)\log T$ times asymptotically (corrected: $p_g>0$)
-- statement:
--   Let $\mathcal I$ be a grouped $K$-armed bandit instance with parameter $\theta\in(0,1)^K$ (distinct entries). For any $a\in\mathcal A_{\mathrm{sub}}$, PF-UCB satisfies
--   $$\lim_{T\to\infty}\frac{\mathbb E[N_T(a)]}{\log T}=J(a),\qquad J(a)=\max_{g\in G_a}J^g(a).\tag{25}$$
--
--   The total number of pulls of an arm optimal for no group matches the lower bound (8), as for a regret-optimal policy.
--
--   Differences from the source:
--   - correction: p_g ≥ 0 with Σ_g p_g = 1 (p.6) → ∀ g, 0 < p g; reason: with p = (1, 0), A^1 = A^2 = {1, 2}, θ = (0.3, 0.6), the program P(θ̂) is symmetric in the two groups, so q̂^1_t(a) ≤ 1/2 for each arm once both arms have been pulled; step 1 then fires only for the first pull of each arm and PF-UCB is greedy afterwards; with positive probability the single sample of arm 2 lies below every running mean of arm 1, and group 1 then pulls the suboptimal arm 1 greedily at every later step, so E[N_T(1)]/log T → ∞, not J(1); the proofs use p_g > 0 throughout (W^g_t, p.34; Claim 3, p.44; p.61)
--   - encoding: A^g unrestricted → every A^g nonempty; reason: OPT(g) = max over A^g and the pull A_t ∈ A^{g_t} are undefined otherwise
--   - encoding: G_a unrestricted → every arm belongs to some group; reason: J(a) = max over G_a is undefined otherwise and (13) is infeasible (Σ_g q^g(a) = 1 with every q^g(a) = 0)
--   - reading: UCB_t(a) = max{q : N_t(a)KL(θ̂_t(a), q) ≤ log t + 3 log log t}, θ̂_t empirical mean → f(1) = f(2) = f(3) = log 3 + 3 log log 3, UCB = +∞ and θ̂ = 0 for an unpulled arm; reason: log log t is undefined at t = 1 and negative at t = 2, and θ̂ of an unpulled arm is undefined; the convention is that of the published CappeKLUCB_ExpFam_Setting, and the result is asymptotic
--   - generalization: PF-UCB with an unspecified choice in each "∈ arg max" → PF-UCB with every tie-breaking rule sel; reason: a statement for every rule specializes to the paper policy whatever choice it makes
--   - encoding: A = [K], G a finite set → any finite linearly ordered arm type and any finite group type with the discrete σ-algebra; reason: every finite set of arms is order-isomorphic to [K]; the order is only used to index the uniform choice in step 1 of PF-UCB
--   - encoding: times t = 1, 2, …; Pr and E → Lean step s is paper time s + 1; probabilities are measures of events, expectations are ∫⁻ of nonnegative quantities; reason: Lean indexing; same values
-- source:
--   Baek & Farias, Fair Exploration via Axiomatic Bargaining, arXiv:2106.02553v2, Proposition 11, (25), p.40 (proof p.43)

import Mathlib
import Definitions.Def_FairExplore_Policies

open Filter Topology

namespace FairExplore

/-- Proposition 11: for any `a ∈ A_sub`, PF-UCB satisfies `lim_{T→∞} E[N_T(a)]/log T = J(a)` (25).
Baek & Farias, *Fair Exploration via Axiomatic Bargaining*, arXiv:2106.02553v2, Proposition 11, p.40 (proof p.43).

**Formalization Note** For every tie-breaking selector `sel`. `N_T(a)` counts the pulls in paper
times `1, …, T`. -/
theorem proposition_11 {γ α : Type*} [Fintype γ] [MeasurableSpace γ] [DiscreteMeasurableSpace γ] [DecidableEq γ]
    [Fintype α] [LinearOrder α]
    (S : GroupedStructure γ α) (hp : ∀ g, 0 < S.p g) (hA : ∀ g, (S.A g).Nonempty)
    (hG : ∀ a, ∃ g, a ∈ S.A g) (θ : α → ℝ) (hθ : InKClass θ)
    (sel : Finset α → α) (hsel : IsSelector sel)
    (a : α) (ha : a ∈ subAll S.A θ) :
    Tendsto (fun T : ℕ => expPulls S θ (pfucb S.A sel) T a / Real.log T) atTop
      (𝓝 (Jmax S.A θ a)) := by sorry

end FairExplore
