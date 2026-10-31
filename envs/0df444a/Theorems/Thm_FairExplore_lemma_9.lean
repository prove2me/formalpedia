-- Prove2me | Theorems.Thm_FairExplore_lemma_9
-- name    : FairExplore.lemma_9
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:17:58.731676+00:00
-- url     : https://prove2.me/theorems/9413b59a-7113-4eda-b581-abff52feec1a
-- title:
--   Lemma 9, p.45 — PF-UCB is log-consistent (corrected: $p_g>0$)
-- statement:
--   For every grouped $K$-armed bandit structure, the PF-UCB policy (with any tie-breaking rule) is log-consistent in the sense of Definition 2: for every parameter $\theta\in(0,1)^K$ with distinct entries and every group $g$,
--   $$\mathbb E\Big[\sum_{a\in\mathcal A^g_{\mathrm{sub}}}N^g_T(a)\Big]=O(\log T).$$
--
--   This lets Propositions 8 and 9 and Lemma 4 be applied to PF-UCB.
--
--   Differences from the source:
--   - correction: p_g ≥ 0 with Σ_g p_g = 1 (p.6) → ∀ g, 0 < p g; reason: with p = (1, 0), A^1 = A^2 = {1, 2}, θ = (0.3, 0.6), the program P(θ̂) is symmetric in the two groups, so q̂^1_t(a) ≤ 1/2 for each arm once both arms have been pulled; step 1 then fires only for the first pull of each arm and PF-UCB is greedy afterwards; with positive probability the single sample of arm 2 lies below every running mean of arm 1, and group 1 then pulls the suboptimal arm 1 greedily at every later step, so E[N^1_T(1)] grows linearly in T and PF-UCB is not log-consistent; the proofs use p_g > 0 throughout (W^g_t, p.34; Claim 3, p.44; p.61)
--   - encoding: A^g unrestricted → every A^g nonempty; reason: OPT(g) = max over A^g and the pull A_t ∈ A^{g_t} are undefined otherwise
--   - encoding: G_a unrestricted → every arm belongs to some group; reason: J(a) = max over G_a is undefined otherwise and (13) is infeasible (Σ_g q^g(a) = 1 with every q^g(a) = 0)
--   - reading: consistency / log-consistency over every instance of the class → over every θ ∈ (0,1)^K with distinct entries, the structure (G, p, A^g) fixed; reason: the policy knows every quantity except θ (p.6), so the class it is designed for varies θ
--   - reading: UCB_t(a) = max{q : N_t(a)KL(θ̂_t(a), q) ≤ log t + 3 log log t}, θ̂_t empirical mean → f(1) = f(2) = f(3) = log 3 + 3 log log 3, UCB = +∞ and θ̂ = 0 for an unpulled arm; reason: log log t is undefined at t = 1 and negative at t = 2, and θ̂ of an unpulled arm is undefined; the convention is that of the published CappeKLUCB_ExpFam_Setting, and the result is asymptotic
--   - generalization: PF-UCB with an unspecified choice in each "∈ arg max" → PF-UCB with every tie-breaking rule sel; reason: a statement for every rule specializes to the paper policy whatever choice it makes
--   - encoding: A = [K], G a finite set → any finite linearly ordered arm type and any finite group type with the discrete σ-algebra; reason: every finite set of arms is order-isomorphic to [K]; the order is only used to index the uniform choice in step 1 of PF-UCB
--   - encoding: O(h(T)) as T → ∞, constants depending on the instance and the fixed parameters → ∃ C T₀, ∀ T ≥ T₀, … ≤ C · h(T), with C, T₀ chosen after the instance and the fixed parameters; reason: App. B.1, p.31
--   - encoding: times t = 1, 2, …; Pr and E → Lean step s is paper time s + 1; probabilities are measures of events, expectations are ∫⁻ of nonnegative quantities; reason: Lean indexing; same values
-- source:
--   Baek & Farias, Fair Exploration via Axiomatic Bargaining, arXiv:2106.02553v2, Lemma 9, p.45 (proof p.47)

import Mathlib
import Definitions.Def_FairExplore_Policies

namespace FairExplore

/-- Lemma 9: PF-UCB is log-consistent. Baek & Farias, *Fair Exploration via Axiomatic Bargaining*, arXiv:2106.02553v2, Lemma 9, p.45 (proof p.47).

**Formalization Note** For every tie-breaking selector `sel`; log-consistency over the K-armed class
with the known structure `S` (Definition 2, p.32). -/
theorem lemma_9 {γ α : Type*} [Fintype γ] [MeasurableSpace γ] [DiscreteMeasurableSpace γ] [DecidableEq γ]
    [Fintype α] [LinearOrder α]
    (S : GroupedStructure γ α) (hp : ∀ g, 0 < S.p g) (hA : ∀ g, (S.A g).Nonempty)
    (hG : ∀ a, ∃ g, a ∈ S.A g) (sel : Finset α → α) (hsel : IsSelector sel) :
    IsLogConsistent S (pfucb S.A sel) := by sorry

end FairExplore
