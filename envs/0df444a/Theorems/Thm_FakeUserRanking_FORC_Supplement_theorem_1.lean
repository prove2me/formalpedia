-- Prove2me | Theorems.Thm_FakeUserRanking_FORC_Supplement_theorem_1
-- name    : FakeUserRanking.FORC.Supplement.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T10:33:37.865677+00:00
-- url     : https://prove2.me/theorems/b6917225-05b1-4f2c-9b29-7292411abf9e
-- title:
--   Theorem 1, p. 14 — some two-product instance and O(log²T) fake users make UCB incur Ω(T) regret
-- statement:
--   **Theorem 1 (non-robustness of UCB to fake users).** There is an instance of the product-ranking problem with two products, with click probabilities $\mu_1>\mu_2$ and some exit probability, and there are constants $C$, $c>0$ and $T_0$ with the following property. For every horizon $T\ge T_0$ and every tie-breaking rule of the UCB algorithm (27), there are a fakeness budget $F$ with
--
--   $$F\le C\,(\log T)^2$$
--
--   and a deterministic adaptive fake-user policy $P$ with fakeness budget $F$ such that UCB's regret against $P$ satisfies
--
--   $$\mathrm{Reg}_T(P)\;\ge\;c\,T.$$
--
--   Here the regret is (2) for the fixed policy $P$: the expected number of clicks by real users when the optimal ranking $\pi^\star=(1,2)$ is displayed in every round, minus the expected number of clicks by real users under UCB, both runs facing the same policy $P$.
--
--   A small number of fake users, $O(\log^2T)$, thus suffices to make the standard UCB algorithm, and so CascadeUCB-type algorithms for ranking, lose a constant fraction of all clicks. This motivates the fakeness-aware algorithms FAR and FORC.
--
--   **Formalization Note** The instance is fixed before the constants, and the constants before $T$. The fake-user policy is chosen after the horizon and UCB's tie-breaking rule. It is a function of the history $H_{t-1}$ of past rankings, fake indicators and observations, as in the published model; since UCB is deterministic, the policy can recompute UCB's current ranking from that history. Products are `Fin 2`, indexed from $0$. The logarithm is natural, and $\log^2T$ means $(\log T)^2$.
--
--   Differences from the source:
--   - encoding: products, positions and rounds are numbered from 1 → products and positions are `Fin n` and rounds are trajectory indices, all numbered from 0; reason: a relabelling; every instance of the paper corresponds to exactly one Lean instance
--   - reading: F = O(log²(T)) fake users and Ω(T) regret, for "the UCB algorithm", whose ties are "broken arbitrarily" (p. 45) → ∃ instance with μ strictly decreasing, then ∃ C, c > 0, T₀, ∀ T ≥ T₀, ∀ tie-breaking rule, ∃ F ≤ C (log T)² and a policy within budget F with regret ≥ c T; reason: the asymptotic notation is read with existential constants placed before T, and the claim is made for every resolution of UCB's unspecified ties, the fake users being chosen after it as in Appendix B
--   - reading: UCB_i = μ̂_i + √(log T/η_i) (27), undefined at η_i = 0 → UCB_i = +∞ while η_i = 0; reason: Appendix B, p. 45, item 1, uses that UCB places the product with the smaller feedback count first, which at η = 0 is the convention UCB_i = +∞
--   - encoding: Reg_T is a supremum over fake-user policies P ∈ 𝒫, and the fake users are a "sequence" → the regret of one exhibited deterministic policy within budget F is at least c T; reason: a lower bound for one feasible policy is a lower bound for the supremum, and a deterministic policy is a feasible (randomized) policy
-- source:
--   Golrezaei, Manshadi, Schneider, Sekar, Learning Product Rankings Robust to Fake Users, arXiv:2009.05138v1, p. 14, Theorem 1; proof in Appendix B, pp. 44–46; UCB index (27), p. 45

import Mathlib
import Definitions.Def_FakeUserRanking_FORC_Model
import Definitions.Def_FakeUserRanking_FORC_Supplement_UCB

namespace FakeUserRanking.FORC.Supplement

/-- Theorem 1 (Non-Robustness of UCB to Fake Users), p. 14: there is a two-product instance with
`μ₁ > μ₂` and absolute constants `C`, `c > 0`, `T₀` such that for every horizon `T ≥ T₀` and every
tie-breaking rule of UCB, some deterministic adaptive fake-user policy with fakeness budget
`F ≤ C (log T)²` makes UCB's regret at least `c T`. -/
theorem theorem_1 :
    ∃ inst : Instance 2, StrictAnti inst.μ ∧
    ∃ C c T₀ : ℝ, 0 < c ∧ ∀ T : ℕ, T₀ ≤ T →
      ∀ tb : List (Fin 1 × Obs 2) → Fin 2,
      ∃ F : ℕ, (F : ℝ) ≤ C * Real.log T ^ 2 ∧
      ∃ a : List (PubStep 2) → Action 2,
        WithinBudget F (fun h => PMF.pure (a h)) ∧
        c * T ≤ regret inst (fun h => PMF.pure (a h)) (ucb T tb) T := by sorry

end FakeUserRanking.FORC.Supplement
