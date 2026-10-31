-- Prove2me | Theorems.Thm_FairExplore_theorem_3
-- name    : FairExplore.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:19:10.662975+00:00
-- url     : https://prove2.me/theorems/3ba6e341-3d6c-4609-9559-91e866c3c903
-- title:
--   Theorem 3, p.15 — PF-UCB attains the Nash welfare bound: $SW(\pi^{\mathrm{PF\text{-}UCB}},\mathcal I)=Y^*(\mathcal I)$ (corrected: $p_g>0$)
-- statement:
--   For any instance $\mathcal I$ of grouped $K$-armed bandits — finitely many groups $G$ arriving i.i.d. with probabilities $p_g$, action sets $\mathcal A^g\subseteq\mathcal A$, Gaussian rewards $\mathrm{Normal}(\theta(a),1)$ with $\theta\in(0,1)^K$ having distinct entries — the PF-UCB policy satisfies
--   $$SW(\pi^{\mathrm{PF\text{-}UCB}},\mathcal I)=Y^*(\mathcal I),$$
--   where $SW(\pi,\mathcal I)=\sum_{g}\log\mathrm{UtilGain}^g(\pi,\mathcal I)$ is the Nash social welfare (4) with utility gains (3) measured against the disagreement point $\tilde R^g_T(\mathcal I)$ (KL-UCB on the single-group instance $\mathcal I_g$), and $Y^*(\mathcal I)$ is the optimal value of program (13).
--
--   With Theorem 2 ($SW(\pi,\mathcal I)\le Y^*(\mathcal I)$ for every consistent $\pi$) this makes PF-UCB the Nash solution, i.e. proportionally fair.
--
--   **Formalization Note** Both sides are extended reals ($\log u=-\infty$ for $u\le0$); $Y^*$ is the supremum of the objective of (13) over its feasible set.
--
--   Differences from the source:
--   - correction: p_g ≥ 0 with Σ_g p_g = 1 (p.6) → ∀ g, 0 < p g; reason: with p = (1, 0), A^1 = A^2 = {1, 2}, θ = (0.3, 0.6), group 2 never arrives, so R^2_T = R̃^2_T = 0, UtilGain^2 = 0 and SW = −∞, while Y* = 2 log(10/3); the proofs use p_g > 0 throughout (W^g_t, p.34; Claim 3, p.44; p.61)
--   - encoding: A^g unrestricted → every A^g nonempty; reason: OPT(g) = max over A^g and the pull A_t ∈ A^{g_t} are undefined otherwise
--   - encoding: G_a unrestricted → every arm belongs to some group; reason: J(a) = max over G_a is undefined otherwise and (13) is infeasible (Σ_g q^g(a) = 1 with every q^g(a) = 0)
--   - reading: UCB_t(a) = max{q : N_t(a)KL(θ̂_t(a), q) ≤ log t + 3 log log t}, θ̂_t empirical mean → f(1) = f(2) = f(3) = log 3 + 3 log log 3, UCB = +∞ and θ̂ = 0 for an unpulled arm; reason: log log t is undefined at t = 1 and negative at t = 2, and θ̂ of an unpulled arm is undefined; the convention is that of the published CappeKLUCB_ExpFam_Setting, and the result is asymptotic
--   - generalization: PF-UCB with an unspecified choice in each "∈ arg max" → PF-UCB with every tie-breaking rule sel; reason: a statement for every rule specializes to the paper policy whatever choice it makes
--   - generalization: the disagreement point uses KL-UCB with an unspecified choice among arms of equal UCB → every tie-breaking rule selD for the KL-UCB of the disagreement point; reason: a statement for every rule specializes to whatever choice the paper makes
--   - encoding: SW, UtilGain, log and the max in (13) in the extended reals → EReal; liminf in EReal; Y* = sSup of the objective over the feasible set; reason: log u = −∞ for u ≤ 0 needs −∞; the sup equals the max when attained (min_norm_solution_exists_unique)
--   - reading: I_g has the action set A ∩ {a₀} → arms Option α (none = a₀); the null action pays the deterministic reward 0; reason: the printed ∩ is a typo for ∪; "we receive no reward under any action" (p.8)
--   - encoding: A = [K], G a finite set → any finite linearly ordered arm type and any finite group type with the discrete σ-algebra; reason: every finite set of arms is order-isomorphic to [K]; the order is only used to index the uniform choice in step 1 of PF-UCB
--   - encoding: times t = 1, 2, …; Pr and E → Lean step s is paper time s + 1; probabilities are measures of events, expectations are ∫⁻ of nonnegative quantities; reason: Lean indexing; same values
-- source:
--   Baek & Farias, Fair Exploration via Axiomatic Bargaining, arXiv:2106.02553v2, Theorem 3, p.15 (proof: Appendix E, p.40)

import Mathlib
import Definitions.Def_FairExplore_Welfare

namespace FairExplore

/-- Theorem 3: for any instance `I` of grouped K-armed bandits, `SW(π^PF-UCB, I) = Y*(I)`.
Baek & Farias, *Fair Exploration via Axiomatic Bargaining*, arXiv:2106.02553v2, Theorem 3, p.15 (proof App. E, p.40).

**Formalization Note** Every structure (finite groups and arms, action sets, arrival probabilities)
and parameter `θ ∈ (0,1)^K` with distinct entries. Correction: every group arrives with positive
probability (`p_g > 0`); with `p = (1, 0)` the printed statement fails. Encodings: every group has an
arm and every arm has a group. PF-UCB breaks ties with any selector `sel`, and the KL-UCB policy of
the disagreement point with any selector `selD`. `SW` and `Y*` are in `EReal`. -/
theorem theorem_3 {γ α : Type*} [Fintype γ] [MeasurableSpace γ] [DiscreteMeasurableSpace γ] [DecidableEq γ]
    [Fintype α] [LinearOrder α]
    (S : GroupedStructure γ α) (hp : ∀ g, 0 < S.p g) (hA : ∀ g, (S.A g).Nonempty)
    (hG : ∀ a, ∃ g, a ∈ S.A g) (θ : α → ℝ) (hθ : InKClass θ)
    (sel : Finset α → α) (hsel : IsSelector sel)
    (selD : Finset (Option α) → Option α) (hselD : IsSelector selD) :
    SW S θ selD (pfucb S.A sel) = Ystar S.A θ := by sorry

end FairExplore
