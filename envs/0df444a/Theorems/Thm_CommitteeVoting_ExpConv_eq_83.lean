-- Prove2me | Theorems.Thm_CommitteeVoting_ExpConv_eq_83
-- name    : CommitteeVoting.ExpConv.eq_83
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:42:34.009978+00:00
-- url     : https://prove2.me/theorems/2ba1fcd1-b481-4820-b02c-540a9fc962ec
-- title:
--   (83), p. 48 — every member of ℋ outscores every dishonest producer with probability at least 1 − 2m²e^{−δ²n/2}
-- statement:
--   Let $n$ voters cast independent random approval ballots over $m$ producers, with $p_{ij}=\Pr[j\in\mathcal C_{v_i}]$, and let $X_j$ be the number of votes of producer $j$. Let $\mathcal M$ be the set of dishonest producers and $\mathcal H$ a set of producers disjoint from $\mathcal M$, and let $\delta>0$ satisfy
--   $$\min_{i\in[n],\,j\in\mathcal H}p_{ij}\ \ge\ \max_{i\in[n],\,j\in\mathcal M}p_{ij}+\delta .$$
--   Then all members of $\mathcal H$ receive more votes than all members of $\mathcal M$ with probability
--   $$\Pr\bigl[\,X_{j_m}<X_{j_h}\ \text{ for all } j_h\in\mathcal H,\ j_m\in\mathcal M\,\bigr]\ \ge\ 1-2m^2e^{-\delta^2 n/2}.$$
--
--   Together with the deterministic reduction at the start of the proof of Theorem 3, this gives the main result.
--
--   **Formalization Note** The min/max gap is stated pairwise: $p_{i'j_m}+\delta\le p_{ij_h}$ for all voters $i,i'$, all $j_h\in\mathcal H$ and $j_m\in\mathcal M$. This is equivalent when $\mathcal H$ and $\mathcal M$ are nonempty, and avoids an undefined minimum or maximum otherwise. The cardinality condition $|\mathcal H|\ge(1-p)k$ of Theorem 3 is not needed for (83) and is not assumed. Ballots of different voters are independent (§5.1.2); the ballot law is otherwise arbitrary.
-- source:
--   Benhaim, Falk, Tsoukalas, Scaling Blockchains: Can Committee-based Consensus Help?, arXiv:2110.08673v2, p. 48, Proof of Theorem 3, eq. (83)

import Mathlib
import Definitions.Def_CommitteeVoting_ExpConv_Committee
import Definitions.Def_CommitteeVoting_ExpConv_VoteProb

open MeasureTheory ProbabilityTheory

namespace CommitteeVoting.ExpConv
theorem eq_83 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n m : ℕ} (ballot : Fin n → Ω → Fin m → Bool) (hmeas : ∀ i, Measurable (ballot i))
    (hind : iIndepFun ballot P) (Mal H : Finset (Fin m)) (hdisj : Disjoint H Mal)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ i i' : Fin n, ∀ jh ∈ H, ∀ jm ∈ Mal,
      voteProb P ballot i' jm + δ ≤ voteProb P ballot i jh) :
    1 - 2 * (m : ℝ) ^ 2 * Real.exp (-(δ ^ 2 * n / 2))
      ≤ P.real {ω | ∀ jh ∈ H, ∀ jm ∈ Mal,
          score (fun i => ballot i ω) jm < score (fun i => ballot i ω) jh} := by sorry
end CommitteeVoting.ExpConv
