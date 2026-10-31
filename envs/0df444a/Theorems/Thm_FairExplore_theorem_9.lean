-- Prove2me | Theorems.Thm_FairExplore_theorem_9
-- name    : FairExplore.theorem_9
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:18:34.677287+00:00
-- url     : https://prove2.me/theorems/7a7fc62c-e9f0-4632-be07-44cc9f94a936
-- title:
--   Theorem 9, p.40 — PF-UCB: $R^g_T/\log T\to\sum_{a\in\mathcal A^g}\Delta^g(a)q^g(a)J(a)$ (corrected: $p_g>0$)
-- statement:
--   Let $\mathcal I$ be an instance of grouped $K$-armed bandits with parameter $\theta\in(0,1)^K$ (distinct entries), and let $q$ be the optimal solution to (13) with the smallest Euclidean norm. Then for all groups $g\in G$,
--   $$\lim_{T\to\infty}\frac{R^g_T(\pi^{\mathrm{PF\text{-}UCB}},\mathcal I)}{\log T}=\sum_{a\in\mathcal A^g}\Delta^g(a)\,q^g(a)\,J(a).$$
--
--   This is (14); Theorem 3 follows by subtracting it from (7).
--
--   **Formalization Note** $J(a)$ is defined by the paper only for $a\in\mathcal A_{\mathrm{sub}}$; for every other arm $q^g(a)=0$ by feasibility, so the value Lean gives $J(a)$ there does not enter.
--
--   Differences from the source:
--   - correction: p_g ≥ 0 with Σ_g p_g = 1 (p.6) → ∀ g, 0 < p g; reason: with p = (1, 0), A^1 = A^2 = {1, 2}, θ = (0.3, 0.6), group 2 never arrives, so R^2_T = 0, while the right side for g = 2 is ∆^2(1)q^2(1)J(1) = 0.3 · (1/2) · 200/9 > 0; the proofs use p_g > 0 throughout (W^g_t, p.34; Claim 3, p.44; p.61)
--   - encoding: A^g unrestricted → every A^g nonempty; reason: OPT(g) = max over A^g and the pull A_t ∈ A^{g_t} are undefined otherwise
--   - encoding: G_a unrestricted → every arm belongs to some group; reason: J(a) = max over G_a is undefined otherwise and (13) is infeasible (Σ_g q^g(a) = 1 with every q^g(a) = 0)
--   - reading: UCB_t(a) = max{q : N_t(a)KL(θ̂_t(a), q) ≤ log t + 3 log log t}, θ̂_t empirical mean → f(1) = f(2) = f(3) = log 3 + 3 log log 3, UCB = +∞ and θ̂ = 0 for an unpulled arm; reason: log log t is undefined at t = 1 and negative at t = 2, and θ̂ of an unpulled arm is undefined; the convention is that of the published CappeKLUCB_ExpFam_Setting, and the result is asymptotic
--   - generalization: PF-UCB with an unspecified choice in each "∈ arg max" → PF-UCB with every tie-breaking rule sel; reason: a statement for every rule specializes to the paper policy whatever choice it makes
--   - encoding: A = [K], G a finite set → any finite linearly ordered arm type and any finite group type with the discrete σ-algebra; reason: every finite set of arms is order-isomorphic to [K]; the order is only used to index the uniform choice in step 1 of PF-UCB
--   - encoding: times t = 1, 2, …; Pr and E → Lean step s is paper time s + 1; probabilities are measures of events, expectations are ∫⁻ of nonnegative quantities; reason: Lean indexing; same values
--   - encoding: J(a) = max_{g ∈ G_a} J^g(a), defined for a ∈ A_sub → Jmax, with J^g(a) = 1/0 = 0 at an arm optimal for g; reason: for a ∉ A_sub the factor q^g(a) is 0 by feasibility, so the sum is unchanged
-- source:
--   Baek & Farias, Fair Exploration via Axiomatic Bargaining, arXiv:2106.02553v2, Theorem 9, p.40 (proof pp.40–41); (14), p.15

import Mathlib
import Definitions.Def_FairExplore_Policies

open Filter Topology

namespace FairExplore

/-- Theorem 9: let `q` be the optimal solution to (13) with the smallest Euclidean norm. Then for
all groups `g`, `lim_{T→∞} R^g_T(π^PF-UCB, I)/log T = ∑_{a ∈ A^g} ∆^g(a) q^g(a) J(a)`.
Baek & Farias, *Fair Exploration via Axiomatic Bargaining*, arXiv:2106.02553v2, Theorem 9, p.40 (proof pp.40–41); also (14), p.15.

**Formalization Note** `q = qhat S.A θ`. `J(a)` is the paper's only for `a ∈ A_sub`; elsewhere
`q^g(a) = 0` (feasibility), so the junk value of `Jmax` does not enter. For every selector `sel`. -/
theorem theorem_9 {γ α : Type*} [Fintype γ] [MeasurableSpace γ] [DiscreteMeasurableSpace γ] [DecidableEq γ]
    [Fintype α] [LinearOrder α]
    (S : GroupedStructure γ α) (hp : ∀ g, 0 < S.p g) (hA : ∀ g, (S.A g).Nonempty)
    (hG : ∀ a, ∃ g, a ∈ S.A g) (θ : α → ℝ) (hθ : InKClass θ)
    (sel : Finset α → α) (hsel : IsSelector sel)
    (g : γ) :
    Tendsto (fun T : ℕ => groupRegretK S θ (pfucb S.A sel) T g / Real.log T) atTop
      (𝓝 (∑ a ∈ S.A g, gap S.A θ g a * qhat S.A θ g a * Jmax S.A θ a)) := by sorry

end FairExplore
