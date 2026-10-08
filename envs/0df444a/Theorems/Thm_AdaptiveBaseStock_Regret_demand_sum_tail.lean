-- Prove2me | Theorems.Thm_AdaptiveBaseStock_Regret_demand_sum_tail
-- name    : AdaptiveBaseStock.Regret.demand_sum_tail
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:28:10.732369+00:00
-- url     : https://prove2.me/theorems/2b6ce60a-0383-4875-96a5-a6fc6554c2e3
-- title:
--   Lemma 5 — P[D₁ + ⋯ + D_t ≤ η] ≤ F(η)^t
-- statement:
--   Let $D_1, D_2, \dots$ be i.i.d. nonnegative continuous demands with $E[D] > 0$ and distribution function $F$, and suppose that $D$ has an infinite support. Then for every $\eta \in \mathbb R$ and every $t \ge 1$,
--   $$\mathcal P\Big[\sum_{\ell=1}^t D_\ell \le \eta\Big] \le F(\eta)^t .$$
--
--   This tail bound controls how long an initial inventory position above $S$ can survive, and it is the input of Lemma 6.
--
--   **Formalization Note** Only the infinite-support case of the paper's lemma is stated; the bounded-demand case is not part of this mission. The sum runs over Lean indices $0, \dots, t-1$, which are the paper's $D_1, \dots, D_t$.
-- source:
--   Huh, Janakiraman, Muckstadt, Rusmevichientong, An Adaptive Algorithm for Finding the Optimal Base-Stock Policy in Lost Sales Inventory Systems with Censored Demand, working paper, February 8, 2007 (published version: Math. Oper. Res., 2009, DOI 10.1287/moor.1080.0367), Lemma 5 (first case), p. 15

import Mathlib
import Definitions.Def_AdaptiveBaseStock_Regret_Model

namespace AdaptiveBaseStock.Regret

open MeasureTheory ProbabilityTheory

/-- Lemma 5 (infinite-support case), p. 15: `P[D_1 + ⋯ + D_t ≤ η] ≤ F(η)^t` for every `η` and
`t ≥ 1`. -/
theorem demand_sum_tail {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : ℕ → Ω → ℝ) (hD : IsDemandModel P D) (hinf : HasInfiniteSupport P (D 0))
    (η : ℝ) (t : ℕ) (ht : 1 ≤ t) :
    P.real {ω | ∑ ℓ ∈ Finset.range t, D ℓ ω ≤ η} ≤ demandCdf P (D 0) η ^ t := by sorry

end AdaptiveBaseStock.Regret
