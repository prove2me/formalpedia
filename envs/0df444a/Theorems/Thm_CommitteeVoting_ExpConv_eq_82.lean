-- Prove2me | Theorems.Thm_CommitteeVoting_ExpConv_eq_82
-- name    : CommitteeVoting.ExpConv.eq_82
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:42:34.023533+00:00
-- url     : https://prove2.me/theorems/fe7b445d-35ea-48a2-a9f2-ed00d6d3f7e7
-- title:
--   (82), p. 48 — for j_h ∈ ℋ and j_m ∈ ℳ, Pr[X_{j_h} ≤ X_{j_m}] ≤ 2e^{−δ²n/2}
-- statement:
--   Let $n$ voters cast independent random approval ballots over $m$ producers, with $p_{ij}=\Pr[j\in\mathcal C_{v_i}]$, and let $X_j$ be the number of votes of producer $j$. Fix two producers $j_h$ and $j_m$ and a $\delta>0$ such that
--   $$p_{i j_h}\ \ge\ p_{i' j_m}+\delta\qquad\text{for all voters } i,i' .$$
--   Then
--   $$\Pr\bigl[X_{j_h}\le X_{j_m}\bigr]\ \le\ 2e^{-\delta^2 n/2}.$$
--
--   In the proof of Theorem 3, $j_h$ is a member of the honest set $\mathcal H$ and $j_m$ a dishonest producer; the bound is the probability that this particular dishonest producer is not outscored by this particular honest one, and is summed over all pairs to obtain (83).
--
--   **Formalization Note** The paper derives (82) through the split (80)/(81) with strict inequalities, which is false when both thresholds coincide with an attained integer value (e.g. $n=2$, $p_{ij_h}=3/4$, $p_{ij_m}=1/4$, $\delta=1/2$, $X_{j_h}=X_{j_m}=1$); the split with non-strict inequalities is correct, and the bound (82) itself is unaffected. Only (82), read as a bound on $\Pr[X_{j_h}\le X_{j_m}]$, is stated. The gap hypothesis is the hypothesis of Theorem 3 restricted to the fixed pair; the ballot law of each voter is otherwise arbitrary.
-- source:
--   Benhaim, Falk, Tsoukalas, Scaling Blockchains: Can Committee-based Consensus Help?, arXiv:2110.08673v2, p. 48, Proof of Theorem 3, eq. (82)

import Mathlib
import Definitions.Def_CommitteeVoting_ExpConv_Committee
import Definitions.Def_CommitteeVoting_ExpConv_VoteProb

open MeasureTheory ProbabilityTheory

namespace CommitteeVoting.ExpConv
theorem eq_82 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n m : ℕ} (ballot : Fin n → Ω → Fin m → Bool) (hmeas : ∀ i, Measurable (ballot i))
    (hind : iIndepFun ballot P) (jh jm : Fin m) {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ i i' : Fin n, voteProb P ballot i' jm + δ ≤ voteProb P ballot i jh) :
    P.real {ω | score (fun i => ballot i ω) jh ≤ score (fun i => ballot i ω) jm}
      ≤ 2 * Real.exp (-(δ ^ 2 * n / 2)) := by sorry
end CommitteeVoting.ExpConv
