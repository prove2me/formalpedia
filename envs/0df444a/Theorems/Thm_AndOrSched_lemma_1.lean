-- Prove2me | Theorems.Thm_AndOrSched_lemma_1
-- name    : AndOrSched.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:32:27.185423+00:00
-- url     : https://prove2.me/theorems/836cf655-97a8-43cc-8197-6819b3711c4c
-- title:
--   Lemma 1, p.7 — Algorithm 1 is a randomized $2\Delta$-approximation
-- statement:
--   Let $I$ be a normalized instance with acyclic AND-precedences and $p_j\in\{0,1\}$, and let $\bar x$ be an optimal solution of LP (1). For $0<\beta\le1$ let $F(\beta)$ be the largest cost of a schedule that Algorithm 1 may return for $\beta$ (over all tie-breakings). Then
--   1. for every $\beta\in(0,1]$ a compatible order exists, and every compatible order gives a feasible schedule;
--   2. $\beta\mapsto 2\beta F(\beta)$ is integrable on $(0,1]$;
--   3. for every feasible schedule $C$,
--   $$\mathbb E[F(\beta)]=\int_0^1 2\beta\,F(\beta)\,d\beta\;\le\;2\Delta\sum_{j\in N}w_jC_j ,$$
--   where $\beta$ is drawn from $(0,1]$ with density $f(\beta)=2\beta$.
--
--   Differences from the source:
--   - encoding: a precedence digraph E∧ → hypothesis `Acyclic I`; reason: a precedence graph is acyclic; the paper's transitive-closure and redundancy assumptions presuppose it
--   - encoding: expected objective of the randomized algorithm vs. the optimum → ∫ 2β F(β) dβ over (0, 1] with F the worst cost over tie-breakings, bounded by 2Δ times the cost of every feasible schedule, plus an integrability clause; reason: covers every tie-breaking and avoids an infimum; integrability makes the bound non-vacuous
--   - encoding: a ρ-approximation is a polynomial-time algorithm → the guarantee is stated for the algorithm on an optimal LP solution; LP solvability is cited by the paper; reason: Mathlib has no complexity model; the guarantee is the mathematical content
-- source:
--   F. Happach, A. S. Schulz, Approximation Algorithms and LP Relaxations for Scheduling Problems Related to Min-Sum Set Cover, arXiv:2001.07011v1, Lemma 1, p.7, with (4), p.8

import Mathlib
import Definitions.Def_AndOrSched_Instance
import Definitions.Def_AndOrSched_Acyclic
import Definitions.Def_AndOrSched_IsFeasible
import Definitions.Def_AndOrSched_cost
import Definitions.Def_AndOrSched_delta
import Definitions.Def_AndOrSched_IsNormalized
import Definitions.Def_AndOrSched_listC
import Definitions.Def_AndOrSched_Compat
import Definitions.Def_AndOrSched_LP1Optimal
import Definitions.Def_AndOrSched_key
import Definitions.Def_AndOrSched_worstCost
open scoped Classical NNReal

namespace AndOrSched

/-- Lemma 1, p.7, with (4), p.8 (Happach, Schulz, arXiv:2001.07011v1): "Algorithm 1 is a randomized 2∆-approximation for
1 | ao-prec = A ∨̇ B, pj ∈ {0, 1} | Σ wjCj."

Let the instance be normalized, with acyclic AND-precedences and processing times at most `1`, and
let `x̄` be an optimal solution of LP (1). Then for every `β ∈ (0, 1]` the `β`-schedules exist and are
feasible, and if `β` is drawn from `(0, 1]` with density `2β`, the expected cost of the `β`-schedule
(for the worst tie-breaking) is at most `2Δ` times the cost of every feasible schedule:
$$\int_0^1 2\beta\,F(\beta)\,d\beta \le 2\Delta\sum_j w_j C_j .$$

**Formalization Note** `F(β) = worstCost` is the largest cost over all orders the algorithm may
output for `β`; the integrability clause makes the bound non-vacuous. -/
theorem lemma_1 (I : Instance) (hI : Acyclic I) (hN : IsNormalized I) (hp : ∀ j, I.p j ≤ 1)
    (x : I.N → ℕ → ℝ) (hx : LP1Optimal I x) :
    (∀ β : ℝ, 0 < β → β ≤ 1 →
      (∃ σ, Compat I (key I x β) σ) ∧ ∀ σ, Compat I (key I x β) σ → IsFeasible I (listC I σ)) ∧
    MeasureTheory.IntegrableOn (fun β : ℝ => 2 * β * worstCost I (key I x β)) (Set.Ioc 0 1) ∧
    ∀ C : I.N → ℝ, IsFeasible I C →
      ∫ β in Set.Ioc (0 : ℝ) 1, 2 * β * worstCost I (key I x β) ≤
        2 * (delta I : ℝ) * cost I C := by sorry

end AndOrSched
