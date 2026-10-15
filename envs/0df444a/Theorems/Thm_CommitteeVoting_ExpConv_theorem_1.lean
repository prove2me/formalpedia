-- Prove2me | Theorems.Thm_CommitteeVoting_ExpConv_theorem_1
-- name    : CommitteeVoting.ExpConv.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:42:33.663843+00:00
-- url     : https://prove2.me/theorems/04ac92f4-fd2d-4d26-95b9-3c159ba05ba3
-- title:
--   Theorem 1, pp. 15–16 — the number of votes of a producer is Poisson binomial with parameters p_{1j}, …, p_{nj}
-- statement:
--   Let $n$ voters cast random approval ballots $\mathcal C_{v_1},\dots,\mathcal C_{v_n}$ over $m$ producers, the ballots of different voters being independent (the approvals inside one ballot may be arbitrarily dependent). For a producer $j$ write $p_{ij}=\Pr[j\in\mathcal C_{v_i}]$ and let $X_j=\operatorname{score}(j)$ be the number of votes $j$ receives. Then for every $x\in\{0,1,2,\dots\}$
--   $$\Pr[X_j=x]\;=\;\sum_{A\in F_x}\ \prod_{i\in A}p_{ij}\prod_{i\in A^{c}}\bigl(1-p_{ij}\bigr),$$
--   where $F_x$ is the family of all $x$-element subsets of the voters $\{1,\dots,n\}$ (empty when $x>n$).
--
--   In the paper the producers' types are fixed by conditioning, and the formula is stated twice, as $f^h$ for an honest producer (with the conditional probabilities $p^h_i$) and as $f^m$ for a dishonest one (with $p^m_i$). It is the distributional fact behind the proof of Theorem 3: $X_j$ is a Poisson binomial random variable with parameters $p_{1j},\dots,p_{nj}$.
--
--   **Formalization Note** The types are fixed and the formula is stated once for an arbitrary producer $j$ with per-producer probabilities $p_{ij}$; the paper's (10) and (11) are the cases where $p_{ij}$ depends only on $i$ and on the type of $j$, so this is a generalisation of the printed statement. The ballot law of each voter is arbitrary (no particular voting strategy is assumed). The printed "$\prod 1-p_{i_2}$" is read as $\prod(1-p_{i_2})$. Independence across voters is the paper's standing assumption of §5.1.2 (p. 15).
-- source:
--   Benhaim, Falk, Tsoukalas, Scaling Blockchains: Can Committee-based Consensus Help?, arXiv:2110.08673v2, pp. 15–16, Theorem 1, eqs. (10)–(11); independence across voters from §5.1.2, p. 15

import Mathlib
import Definitions.Def_CommitteeVoting_ExpConv_Committee
import Definitions.Def_CommitteeVoting_ExpConv_VoteProb

open MeasureTheory ProbabilityTheory

namespace CommitteeVoting.ExpConv
theorem theorem_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n m : ℕ} (ballot : Fin n → Ω → Fin m → Bool) (hmeas : ∀ i, Measurable (ballot i))
    (hind : iIndepFun ballot P) (j : Fin m) (x : ℕ) :
    P.real {ω | score (fun i => ballot i ω) j = x}
      = ∑ A ∈ (Finset.univ : Finset (Fin n)).powersetCard x,
          (∏ i ∈ A, voteProb P ballot i j) * ∏ i ∈ Finset.univ \ A, (1 - voteProb P ballot i j) := by sorry
end CommitteeVoting.ExpConv
