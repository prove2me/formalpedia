-- Prove2me | Theorems.Thm_CommitteeVoting_ExpConv_theorem_3
-- name    : CommitteeVoting.ExpConv.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:42:30.068912+00:00
-- url     : https://prove2.me/theorems/058e86d6-d5be-409c-8003-68844167bb6b
-- title:
--   Theorem 3, p. 22 — with a vote-probability gap δ, Pr[𝕋 = H] ≥ 1 − 2m²e^{−δ²n/2}
-- statement:
--   **Exponential convergence (main result).** Let $n$ voters elect a committee of $k$ block producers out of $m\ge k$ candidates by $k$-winner approval voting, with ties among the lowest elected scores and the filling of an under-full committee resolved adversarially. Let $0\le p\le1$ be the tolerated fraction of dishonest committee members, and call the committee honest, $\mathbb T=H$, when it has at least $\lceil(1-p)k\rceil$ honest members. The ballots of the voters are random and independent across voters; $p_{ij}$ is the probability that voter $i$ votes for producer $j$.
--
--   Let $\mathcal M$ be the set of dishonest producers, and suppose there are a set $\mathcal H$ of honest producers with $|\mathcal H|\ge(1-p)\,k$ and a $\delta>0$ such that
--   $$\min_{i\in[n],\,j\in\mathcal H}p_{ij}\ \ge\ \max_{i\in[n],\,j\in\mathcal M}p_{ij}+\delta .$$
--   Then
--   $$\Pr[\mathbb T=H]\ \ge\ 1-2m^2e^{-\delta^2n/2},$$
--   which tends to $1$ as the number of voters $n$ grows.
--
--   The result holds for every voting strategy, as long as some sufficiently large set of honest producers is approved by every voter with probability at least $\delta$ more than any dishonest producer is approved by any voter.
--
--   **Formalization Note** $\mathbb T=H$ is the event that **every** admissible committee (exactly $k$ members, no outsider scoring above a member) has at least $\lceil(1-p)k\rceil$ members outside $\mathcal M$; this is how the adversarial tie-breaking and filling of Definition 3 are encoded. The producers' types are fixed ($\mathcal M$ is given); the honest producers are the complement of $\mathcal M$, and $\mathcal H$ is any set disjoint from $\mathcal M$. The gap is stated pairwise, $p_{i'j_m}+\delta\le p_{ij_h}$ for all voters $i,i'$, $j_h\in\mathcal H$, $j_m\in\mathcal M$ (equivalent to the min/max form when both sets are nonempty). Added standing assumptions: $k\le m$ (p. 9), $0\le p\le1$ ($p$ is a fraction; the paper never says so), independence of the ballots across voters (§5.1.2), and measurability of each ballot. Each voter's ballot law is otherwise arbitrary, so the Gaussian signal model and the strategy classes of §4 are not formalized and the statement covers them all (the paper: "this result holds across all voting strategy classes"); the cap $|\mathcal C_v|\le t$ of Definition 2 is not imposed. The limit "$\to1$ as $n\to\infty$" is a property of the right-hand side and is not stated separately.
-- source:
--   Benhaim, Falk, Tsoukalas, Scaling Blockchains: Can Committee-based Consensus Help?, arXiv:2110.08673v2, p. 22, Theorem 3, eq. (14); proof in Appendix B.2, p. 48

import Mathlib
import Definitions.Def_CommitteeVoting_ExpConv_Committee
import Definitions.Def_CommitteeVoting_ExpConv_VoteProb

open MeasureTheory ProbabilityTheory

namespace CommitteeVoting.ExpConv
theorem theorem_3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n m k : ℕ} (hkm : k ≤ m) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (ballot : Fin n → Ω → Fin m → Bool) (hmeas : ∀ i, Measurable (ballot i))
    (hind : iIndepFun ballot P) (Mal H : Finset (Fin m)) (hdisj : Disjoint H Mal)
    (hcard : (1 - p) * (k : ℝ) ≤ (H.card : ℝ)) {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ i i' : Fin n, ∀ jh ∈ H, ∀ jm ∈ Mal,
      voteProb P ballot i' jm + δ ≤ voteProb P ballot i jh) :
    1 - 2 * (m : ℝ) ^ 2 * Real.exp (-(δ ^ 2 * n / 2))
      ≤ P.real {ω | IsHonestOutcome k p Malᶜ (score (fun i => ballot i ω))} := by sorry
end CommitteeVoting.ExpConv
