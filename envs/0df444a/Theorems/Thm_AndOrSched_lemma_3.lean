-- Prove2me | Theorems.Thm_AndOrSched_lemma_3
-- name    : AndOrSched.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:33:29.717137+00:00
-- url     : https://prove2.me/theorems/abe4382b-3324-486a-b7ff-938363c175c9
-- title:
--   Lemma 3, p.10 — Algorithm 2 is a randomized $(2\Delta+\varepsilon)$-approximation (corrected: (5f) with $\tau_l\ge p_j$)
-- statement:
--   Let $I$ be a normalized instance with acyclic AND-precedences, $\varepsilon>0$, $\varepsilon'=\varepsilon/(2\Delta)$, and let $\bar x$ be an optimal solution of LP (5). For $0<\beta\le1$ let $F(\beta)$ be the largest cost of a schedule that Algorithm 2 may return for $\beta$. Then
--   1. for every $\beta\in(0,1]$ a compatible order exists, and every compatible order gives a feasible schedule;
--   2. $\beta\mapsto2\beta F(\beta)$ is integrable on $(0,1]$;
--   3. for every feasible schedule $C$,
--   $$\int_0^1 2\beta\,F(\beta)\,d\beta\;\le\;(2\Delta+\varepsilon)\sum_{j\in N}w_jC_j .$$
--
--   Differences from the source:
--   - correction: (5f): x_jl ≥ 0 for l ∈ [L] with τ_{l−1} ≥ p_j (other variables absent) → x_jl ≥ 0 for all l ∈ [L], and x_jl = 0 when τ_l < p_j; reason: as printed LP (5) is infeasible for A = {a}, B = {b}, p_a = 2, p_b = 0, P(b) = {a}, E∧ = ∅, ε′ = 1/2 (τ = (1, 1, 1.5, 2.25), L = 3, no l has τ_{l−1} ≥ 2), although the instance has a feasible schedule; a job completing in (τ_{l−1}, τ_l] has p_j ≤ τ_l
--   - encoding: a precedence digraph E∧ → hypothesis `Acyclic I`; reason: a precedence graph is acyclic; the paper's transitive-closure and redundancy assumptions presuppose it
--   - encoding: expected objective of the randomized algorithm vs. the optimum → ∫ 2β F(β) dβ with F the worst cost over tie-breakings, bounded against every feasible schedule, plus integrability; reason: covers every tie-breaking; integrability makes the bound non-vacuous
--   - encoding: a ρ-approximation is a polynomial-time algorithm → the guarantee for the algorithm on an optimal LP solution; LP solvability is cited by the paper; reason: Mathlib has no complexity model
-- source:
--   F. Happach, A. S. Schulz, Approximation Algorithms and LP Relaxations for Scheduling Problems Related to Min-Sum Set Cover, arXiv:2001.07011v1, Lemma 3, p.10; proof App. A, (29), p.26

import Mathlib
import Definitions.Def_AndOrSched_Instance
import Definitions.Def_AndOrSched_Acyclic
import Definitions.Def_AndOrSched_IsFeasible
import Definitions.Def_AndOrSched_cost
import Definitions.Def_AndOrSched_delta
import Definitions.Def_AndOrSched_IsNormalized
import Definitions.Def_AndOrSched_listC
import Definitions.Def_AndOrSched_Compat
import Definitions.Def_AndOrSched_LP5Optimal
import Definitions.Def_AndOrSched_key
import Definitions.Def_AndOrSched_worstCost
open scoped Classical NNReal

namespace AndOrSched

/-- Lemma 3, p.10, proof in App. A, (29), p.26 (Happach, Schulz, arXiv:2001.07011v1): "Algorithm 2 is a randomized
(2∆ + ε)-approximation for 1 | ao-prec = A ∨̇ B | Σ wjCj, for any ε > 0."

Let the instance be normalized, with acyclic AND-precedences, let `ε > 0`, `ε' = ε/(2Δ)`, and let `x̄`
be an optimal solution of LP (5) (corrected (5f)). Then for every `β ∈ (0, 1]` the `β`-schedules exist
and are feasible, and if `β` is drawn from `(0, 1]` with density `2β`, the expected cost of the
`β`-schedule (for the worst tie-breaking) is at most `2Δ + ε` times the cost of every feasible
schedule.

**Formalization Note** `F(β) = worstCost` as in Lemma 1. (5f) is the corrected constraint. -/
theorem lemma_3 (I : Instance) (hI : Acyclic I) (hN : IsNormalized I) (ε : ℝ) (hε : 0 < ε)
    (x : I.N → ℕ → ℝ) (hx : LP5Optimal I (ε / (2 * (delta I : ℝ))) x) :
    (∀ β : ℝ, 0 < β → β ≤ 1 →
      (∃ σ, Compat I (key I x β) σ) ∧ ∀ σ, Compat I (key I x β) σ → IsFeasible I (listC I σ)) ∧
    MeasureTheory.IntegrableOn (fun β : ℝ => 2 * β * worstCost I (key I x β)) (Set.Ioc 0 1) ∧
    ∀ C : I.N → ℝ, IsFeasible I C →
      ∫ β in Set.Ioc (0 : ℝ) 1, 2 * β * worstCost I (key I x β) ≤
        (2 * (delta I : ℝ) + ε) * cost I C := by sorry

end AndOrSched
