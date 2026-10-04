-- Prove2me | Theorems.Thm_DermanSeqDecisions_Ratio_ratio_stationary_randomized
-- name    : DermanSeqDecisions.Ratio.ratio_stationary_randomized
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T10:46:10.766916+00:00
-- url     : https://prove2.me/theorems/bf3cb1aa-335a-4047-9e60-23095b69710f
-- title:
--   Ratio criterion of a stationary randomized procedure under Assumption A
-- statement:
--   Consider a controlled Markov chain with finitely many states $0, \dots, L$ and decisions $d_1, \dots, d_K$, all available in every state, with transition probabilities $q_{ij}(k)$, and assume Assumption A: for every stationary randomized rule the induced chain has a single class. Let $w'_{ik} > 0$ and $w''_{ik} > 0$ be two sets of costs. Let $R \in C'$ choose decision $d_k$ in state $s$ with probability $D_{sk}$ ($D_{sk} \ge 0$, $\sum_k D_{sk} = 1$), whatever the past, and let $\pi$ satisfy (5) for $p_{sj} = \sum_k q_{sj}(k) D_{sk}$:
--   $$\pi_j \ge 0, \qquad \pi_j - \sum_s \pi_s p_{sj} = 0, \qquad \sum_j \pi_j = 1 .$$
--   Then for every initial state $i$,
--   $$\psi_R(i) = \frac{\sum_{s=0}^{L} \sum_{k=1}^{K} \pi_s D_{sk} w'_{sk}}{\sum_{s=0}^{L} \sum_{k=1}^{K} \pi_s D_{sk} w''_{sk}} .$$
--
--   This display (p. 23) reduces the minimization of $\psi$ over $C'$ to the fractional program of the lemma of §3.
--
--   **Formalization Note** The page uses $i$ both for the initial state and for the summation index; the summation index is renamed $s$. The costs are explicit real arguments; the nonnegative cost field of Sennott's model plays no role.
-- source:
--   Derman, On Sequential Decisions and Markov Chains, Management Science 9(1):16–24 (1962), DOI 10.1287/mnsc.9.1.16, p. 23, §4, unnumbered display before Theorem 3 (with (5), p. 20)

import Mathlib
import Definitions.Def_SennottDP_AvgFinite_Model
import Definitions.Def_DermanSeqDecisions_Ratio_Criteria

open SennottDP.AvgFinite

namespace DermanSeqDecisions.Ratio

/-- **The ratio criterion of a procedure in `C′` under Assumption A** (Derman, *On Sequential
Decisions and Markov Chains*, Management Science 9(1):16–24 (1962), DOI 10.1287/mnsc.9.1.16,
§4, unnumbered display, p. 23).

Let `w′ > 0`, `w″ > 0` be two cost sets, let `θ ∈ C′` choose decision `k` in state `s` with
probability `D_sk`, assume Assumption A, and let `π` satisfy (5) (p. 20) for the induced
transition matrix `p_sj = ∑_k q_sj(k) D_sk`. Then for every initial state `i`,
`ψ_θ(i) = (∑_s ∑_k π_s D_sk w′_sk) / (∑_s ∑_k π_s D_sk w″_sk)`.

**Formalization Note.** The page writes the summation index as `i`, the same letter as the
initial state; here it is `s`. (5) is stated as `π_j ≥ 0`, `π_j − ∑_s π_s p_sj = 0`,
`∑_j π_j = 1`. `M.C` plays no role. -/
theorem ratio_stationary_randomized {S Act : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype Act] [DecidableEq Act] (M : MDC S Act) (hA : ∀ s, M.A s = Finset.univ)
    (hAssA : AssumptionA M)
    (w' w'' : S → Act → ℝ) (hw' : ∀ s a, 0 < w' s a) (hw'' : ∀ s a, 0 < w'' s a)
    (θ : Policy M) (D : S → Act → ℝ) (hD0 : ∀ s a, 0 ≤ D s a) (hD1 : ∀ s, ∑ a, D s a = 1)
    (hθ : IsStationaryRandomized θ D)
    (π : S → ℝ) (hπ0 : ∀ j, 0 ≤ π j)
    (hπ : ∀ j, π j - ∑ s, π s * inducedMatrix M D s j = 0) (hπ1 : ∑ j, π j = 1) (i : S) :
    ratioCost θ i w' w'' =
      (∑ s, ∑ a, π s * D s a * w' s a) / (∑ s, ∑ a, π s * D s a * w'' s a) := by sorry

end DermanSeqDecisions.Ratio
