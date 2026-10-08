-- Prove2me | Theorems.Thm_ArapostathisAC_SennottACOI_acoi_avgCost_le
-- name    : ArapostathisAC.SennottACOI.acoi_avgCost_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T15:44:41.62154+00:00
-- url     : https://prove2.me/theorems/2dd476d6-1dc4-475f-a7e3-7ab41ccd4eb1
-- title:
--   Remark 5.8(a), the half used — an ACOI with h bounded below gives J(i, f) ≤ ρ
-- statement:
--   In the countable-state controlled Markov process of §5, let $\rho\in\mathbb R$, let $h:S\to\mathbb R$ be bounded below, and let $f\in\Pi_{SD}$. Suppose that for every state $i$ the series $\sum_jP(j\mid i,f(i))h(j)$ converges and
--   $$\rho+h(i)\ \ge\ c\big(i,f(i)\big)+\sum_jP\big(j\mid i,f(i)\big)\,h(j).$$
--   Then the average cost of $f$ satisfies $J(i,f)\le\rho$ for every state $i$.
--
--   In the proof of Theorem 5.9 this gives $J(i,f)\le\rho^*$ for the limit policy $f$ ("Since $h(\cdot)$ is bounded below, the proof of Theorem 5.1 can be modified to show that $J(i,f)\le\rho^*$").
--
--   **Formalization Note** The paper's Remark 5.8(a) states more: that under (5.16) with $h$ bounded below, $\rho$ *is* the optimal average cost and every minimizing $f$ is AC-optimal. That does not follow for an arbitrary scalar $\rho$: with $h\equiv0$ and $\rho=\sup c$ (bounded $c$), (5.16) holds, yet $\rho$ need not be the optimal cost. Only the inequality $J(i,f)\le\rho$ holds and is used, so only it is stated. The average cost is a $\limsup$ in $[0,\infty]$ and $\rho$ enters as `ENNReal.ofReal ρ`.
-- source:
--   Arapostathis, Borkar, Fernández-Gaucherand, Ghosh, Marcus, Discrete-time controlled Markov processes with average cost criterion: a survey, SIAM J. Control Optim. 31(2) (1993), p. 308, proof of Theorem 5.9 ("Since h(·) is bounded below, …") and Remark 5.8(a), (5.16)

import Mathlib
import Definitions.Def_ArapostathisAC_SennottACOI_CMP
import Definitions.Def_ArapostathisAC_SennottACOI_Assumptions

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace ArapostathisAC.SennottACOI

variable {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]

/-- Remark 5.8(a) (p. 308), the half used in the proof of Theorem 5.9 ("Since h(·) is bounded
below, the proof of Theorem 5.1 can be modified to show that J(i, f) ≤ ρ*"): if `ρ` is a real
number, `h : S → ℝ` is bounded below, `f ∈ Π_SD`, and for every state `i` the series
`Σ_j P(j | i, f(i)) h(j)` converges with `ρ + h(i) ≥ c(i, f(i)) + Σ_j P(j | i, f(i)) h(j)`, then
`J(i, f) ≤ ρ` for every state `i`. The printed remark further claims that `ρ` is the optimal
average cost, which does not follow; that part is not stated. -/
theorem acoi_avgCost_le (M : ArapostathisAC.VanishingDiscount.CMP A) (ρ : ℝ) (h : ℕ → ℝ) (hb : BddBelow (Set.range h))
    (f : StationaryPolicy M) (hsum : ∀ i, Summable (fun j => ArapostathisAC.VanishingDiscount.prob M i (f.1 i) j * h j))
    (hineq : ∀ i, M.c i (f.1 i) + ∑' j, ArapostathisAC.VanishingDiscount.prob M i (f.1 i) j * h j ≤ ρ + h i) (i : ℕ) :
    ArapostathisAC.VanishingDiscount.avgCost M f.toPolicy i ≤ ENNReal.ofReal ρ := by sorry

end ArapostathisAC.SennottACOI
