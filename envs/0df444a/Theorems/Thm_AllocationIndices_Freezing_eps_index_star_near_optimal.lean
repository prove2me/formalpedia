-- Prove2me | Theorems.Thm_AllocationIndices_Freezing_eps_index_star_near_optimal
-- name    : AllocationIndices.Freezing.eps_index_star_near_optimal
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:38:28.54145+00:00
-- url     : https://prove2.me/theorems/3e96d20c-d389-4922-ad55-96b3cc8a51bb
-- title:
--   Corollary 4.16 — an ε-index* policy is within $\varepsilon/(1-a)$ of optimal
-- statement:
--   Let $F$ be a simple family of $k$ alternative bandit processes on a common countable state space, with a common transition kernel $P$, bounded reward $r$ and discount factor $0 < a < 1$, and let $\varepsilon \ge 0$. Let $h$ be an **ε-index\* policy**: it proceeds in stages, and at the start of each stage it chooses, on the basis of the history so far, a bandit $B$ and a positive stopping time $\tau$ of $B$'s own evolution such that
--   $$\nu_\tau(B) = \frac{R_\tau(B)}{W_\tau(B)} \ge \max_j \nu(B_j) - \varepsilon$$
--   (all indices at the current states), continues $B$ up to $\tau$, and then repeats the procedure forever. Then, for every initial state-vector $x$,
--   $$R_h(F, x) \;\ge\; R(F, x) - \frac{\varepsilon}{1 - a},$$
--   where $R_h(F, x)$ is the expected total discounted reward of $h$ and $R(F, x) = \sup_g R_g(F, x)$ is the supremum over all policies $g$.
--
--   The book writes the bound as $R_h(F) \ge R(F) - \varepsilon\gamma^{-1}$, in the continuous-time units of §2.8, where the discount factor is $a = e^{-\gamma}$ and $\gamma^{-1} = \int_0^\infty a^t\,dt$ is the total discounted time. In the discrete-time units of (2.6), with decision times $0, 1, 2, \dots$, indices measured as reward per unit of discrete discounted time $E\sum_{t<\tau} a^t$ and $\varepsilon$ in the same units, the total discounted time is $\sum_{t \ge 0} a^t = (1 - a)^{-1}$ and the bound is $\varepsilon/(1-a)$. At $\varepsilon = 0$ the statement says that every policy that repeatedly continues a bandit of greatest index up to a stopping time attaining its index is optimal.
--
--   The result quantifies the proof of the index theorem by freezing and promotion rules: it bounds the loss of a policy whose stages are only approximately optimal. Its companion for ε-index policies (the continued bandit's index within ε of the largest at every decision time), Theorem 4.18, has the different bound $\varepsilon/(1-a)^2$ in the same units.
--
--   **Formalization Note** The book's ε-bound is in continuous-time index units; it is converted here as follows. For decision times $0, 1, 2, \dots$ the book's index is $\gamma/(1-a)$ times the discrete-time index (2.6), so an ε-index\* policy in discrete units is a $\varepsilon\gamma/(1-a)$-index\* policy in the book's units, and the book's bound $\varepsilon\gamma/(1-a) \cdot \gamma^{-1}$ is $\varepsilon/(1-a)$. This is the convention of the published Theorem 4.18 item `AllocationIndices.eps_index_policy_near_optimal`. Reading $\varepsilon\gamma^{-1} = \varepsilon/\ln(1/a)$ with the discrete index would be false: two one-state bandits paying $\nu$ and $\nu - \varepsilon$, and the policy that always continues the second, lose exactly $\varepsilon/(1-a) > \varepsilon/\ln(1/a)$. Bandits share one kernel on a common state space (the disjoint-union encoding of the published `MarkovBanditPolicy`). The class of ε-index\* policies is defined structurally (`IsEpsIndexStarPolicy`: the policy follows, after every history, a staged rule whose every stage satisfies the condition above), never through the value of the policy. $R(F, x)$ is the supremum of the published `markovBanditDiscountedValue` over all `MarkovBanditPolicy`s, which is finite since rewards are bounded.
-- source:
--   Gittins, Glazebrook and Weber, Multi-armed Bandit Allocation Indices, 2nd ed., Wiley 2011, doi:10.1002/9780470980033, §4.10 p. 112, Corollary 4.16 (ε-index* policies defined pp. 111–112)

import Definitions.Def_AllocationIndices_Freezing_Model

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace AllocationIndices.Freezing

theorem eps_index_star_near_optimal {T : Type*} [MeasurableSpace T] [Countable T]
    [MeasurableSingletonClass T] (P : Kernel T T) [IsMarkovKernel P] {r : T → ℝ}
    (hr : BoundedReward r) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {ε : ℝ} (hε : 0 ≤ ε) {k : ℕ}
    {π : MarkovBanditPolicy k T} (hπ : IsEpsIndexStarPolicy P r a ε π) (x : Fin k → T) :
    (⨆ π' : MarkovBanditPolicy k T, markovBanditDiscountedValue P r a π' x) - ε / (1 - a) ≤
      markovBanditDiscountedValue P r a π x := by sorry

end AllocationIndices.Freezing
