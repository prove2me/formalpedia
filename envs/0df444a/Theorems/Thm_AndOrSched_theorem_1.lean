-- Prove2me | Theorems.Thm_AndOrSched_theorem_1
-- name    : AndOrSched.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:33:49.132347+00:00
-- url     : https://prove2.me/theorems/3bb84545-7155-4ab1-b015-01bc69e21a51
-- title:
--   Theorem 1, p.4 — $2\Delta$ for $p_j\in\{0,1\}$ and $2\Delta+\varepsilon$ in general (corrected: (5f) with $\tau_l\ge p_j$)
-- statement:
--   Let $I$ be an instance of $1\,|\,\text{ao-prec}=A\dot\vee B\,|\,\sum w_jC_j$ with acyclic AND-precedences and arbitrary weights $w_j\ge0$ on all jobs, let $\Delta=\Delta(I)$ be computed after removing redundant OR-arcs, let $I'$ be the normalized instance with $n'\le2n$ jobs and horizon $T'$, and $\Delta'=\Delta(I')$.
--
--   **(i) A $2\Delta$-approximation for $p_j\in\{0,1\}$.** If every $p_j\in\{0,1\}$, then LP (1) of $I'$ has an optimal solution, and for every optimal $\bar x$:
--   1. for every $\beta\in(0,1]$ some order compatible with the keys and tie rules of Algorithm 1 exists, and every such order yields a feasible schedule of $I$;
--   2. the candidate set $\mathcal B(\bar x)$ lies in $(0,1]$, $T'\le n'$, and $|\mathcal B(\bar x)|\le n'T'+1$;
--   3. some $\beta\in\mathcal B(\bar x)$ yields, for every compatible order, a schedule $C^{\mathrm{alg}}$ of $I$ with
--   $$\sum_{j\in N}w_jC^{\mathrm{alg}}_j\;\le\;2\Delta\sum_{j\in N}w_jC_j\qquad\text{for every feasible schedule }C\text{ of }I .$$
--
--   **(ii) A $(2\Delta+\varepsilon)$-approximation in general.** For every $\varepsilon>0$, with $\varepsilon'=\varepsilon/(2\Delta')$, LP (5) of $I'$ has an optimal solution, and for every optimal $\bar x$ the same holds with the keys of Algorithm 2, $|\mathcal B(\bar x)|\le n'L+1$, $L\le2+(1+\varepsilon')\log T'/\varepsilon'$ when $T'\ge1$, and ratio $2\Delta+\varepsilon$.
--
--   The derandomized algorithm solves the LP, computes the $\beta$-schedule of each candidate and returns the cheapest, so its cost is at most that of the candidate in clause 3.
--
--   Differences from the source:
--   - correction: (5f): x_jl ≥ 0 for l ∈ [L] with τ_{l−1} ≥ p_j (other variables absent) → x_jl ≥ 0 for all l ∈ [L], and x_jl = 0 when τ_l < p_j; reason: as printed LP (5) is infeasible for A = {a}, B = {b}, p_a = 2, p_b = 0, P(b) = {a}, E∧ = ∅, ε′ = 1/2 (τ = (1, 1, 1.5, 2.25), L = 3, no l has τ_{l−1} ≥ 2), although the instance has a feasible schedule; a job completing in (τ_{l−1}, τ_l] has p_j ≤ τ_l
--   - encoding: a precedence digraph E∧ → hypothesis `Acyclic I`; reason: a precedence graph is acyclic; the paper's transitive-closure and redundancy assumptions presuppose it
--   - encoding: "there is a polynomial-time ρ-approximation algorithm" → the guarantee for the paper's derandomized Algorithms 1 and 2 on every optimal LP solution and every tie-breaking, with the candidate count (≤ n′T′ + 1 with T′ ≤ n′ ≤ 2n, resp. ≤ n′L + 1 with L ≤ 2 + (1 + ε′) log T′ / ε′) explicit; LP solvability in polynomial time is cited by the paper; reason: Mathlib has no complexity model, and an existential "∃ algorithm" without one is trivially true
--   - reading: "such a job can be disregarded" (zero-time jobs without predecessors) → the closed set Z of zero-time jobs is scheduled at time 0 and OR-successors of Z lose their OR-constraint; reason: literal deletion can raise the optimum
--   - reading: processing times p_j ≥ 0 in part (ii), "all data is integer" w.l.o.g. → processing times in ℚ≥0, scaled by the lcm of their denominators; reason: the input of an algorithm is rational; real processing times are not an algorithmic input
--   - reading: ε′ = ε/(2∆) for Algorithm 2 → ε′ = ε/(2Δ′) with Δ′ the parameter of the normalized instance on which the algorithm runs; reason: the algorithm runs on the normalized instance; 2Δ′(1 + ε′) = 2Δ′ + ε ≤ 2Δ + ε
--   - encoding: ∆ := max_{b∈B} |P(b)| on an instance with E∧ transitively closed and no redundant OR-arcs (w.l.o.g., p.4), ∆ = 1 when every P(b) = ∅ (p.7) → `delta I` = max(1, max_b |nonRedPred I b|) on every instance, redundancy taken through the transitive closure of the AND-arcs; reason: equal to the paper's ∆ on every instance satisfying its w.l.o.g. assumptions, and on any other instance it is the ∆ of the reduced instance the paper passes to
--   - encoding: ρ times "the optimal objective value" (over orderings of the jobs) → ρ times the cost of every feasible schedule (completion-time vectors, idle time allowed); reason: equivalent, since an optimal schedule exists and has no idle time, and removing idle time raises no completion time; avoids an infimum
-- source:
--   F. Happach, A. S. Schulz, Approximation Algorithms and LP Relaxations for Scheduling Problems Related to Min-Sum Set Cover, arXiv:2001.07011v1, Theorem 1, p.4, "There is a 2∆-approximation algorithm for 1 | ao-prec = A ∨̇ B, pj ∈ {0, 1} | Σ wjCj. Moreover, for any ε > 0, there is a (2∆ + ε)-approximation algorithm for 1 | ao-prec = A ∨̇ B | Σ wjCj."

import Mathlib
import Definitions.Def_AndOrSched_Instance
import Definitions.Def_AndOrSched_Acyclic
import Definitions.Def_AndOrSched_IsFeasible
import Definitions.Def_AndOrSched_cost
import Definitions.Def_AndOrSched_delta
import Definitions.Def_AndOrSched_normalize
import Definitions.Def_AndOrSched_outSched
import Definitions.Def_AndOrSched_Compat
import Definitions.Def_AndOrSched_horizon
import Definitions.Def_AndOrSched_LP1Optimal
import Definitions.Def_AndOrSched_key
import Definitions.Def_AndOrSched_cand
import Definitions.Def_AndOrSched_numIntervals
import Definitions.Def_AndOrSched_LP5Optimal
open scoped Classical NNReal

namespace AndOrSched

/-- Theorem 1, p.4 (Happach, Schulz, arXiv:2001.07011v1): "There is a 2∆-approximation algorithm for
1 | ao-prec = A ∨̇ B, pj ∈ {0, 1} | Σ wjCj. Moreover, for any ε > 0, there is a
(2∆ + ε)-approximation algorithm for 1 | ao-prec = A ∨̇ B | Σ wjCj."

Stated for the paper's derandomized Algorithms 1 and 2. Let `I` have acyclic AND-precedences, let
`I' = normalize I` and `Δ' = Δ(I')`.

(i) If every `pⱼ ∈ {0, 1}`: LP (1) of `I'` has an optimal solution; for every optimal `x̄` and every
`β ∈ (0, 1]` some tie-breaking order exists and every order the algorithm may take yields a feasible
schedule of `I`; the candidate set of `β`'s lies in `(0, 1]` and has at most `n'·T' + 1` elements with
`T' ≤ n' ≤ 2n`; and some candidate `β` gives, for every tie-breaking, a schedule of cost at most
`2Δ` times the cost of every feasible schedule of `I`.

(ii) For every `ε > 0`, with `ε' = ε/(2Δ')` and LP (5) of `I'` (corrected (5f)): the same, with at most
`n'·L + 1` candidates, `L ≤ 2 + (1 + ε') log T' / ε'` when `T' ≥ 1`, and ratio `2Δ + ε`.

**Formalization Note** "There is a polynomial-time algorithm" is stated through the paper's algorithm:
solve the LP (polynomial by the cited LP algorithms), evaluate the `β`-schedule of each candidate and
return the best. Its cost is at most that of the candidate named in the conclusion. `Δ` is computed
after removing redundant OR-arcs. -/
theorem theorem_1 :
    (∀ I : Instance, Acyclic I → (∀ j, I.p j = 0 ∨ I.p j = 1) →
      (∃ x, LP1Optimal (normalize I) x) ∧
      ∀ x, LP1Optimal (normalize I) x →
        (∀ β : ℝ, 0 < β → β ≤ 1 →
          (∃ σ, Compat (normalize I) (key (normalize I) x β) σ) ∧
          ∀ σ, Compat (normalize I) (key (normalize I) x β) σ → IsFeasible I (outSched I σ)) ∧
        (∀ β ∈ cand (normalize I) x (horizon (normalize I)), 0 < β ∧ β ≤ 1) ∧
        horizon (normalize I) ≤ Fintype.card (normalize I).N ∧
        Fintype.card (normalize I).N ≤ 2 * Fintype.card I.N ∧
        (cand (normalize I) x (horizon (normalize I))).card ≤
          Fintype.card (normalize I).N * horizon (normalize I) + 1 ∧
        ∃ β ∈ cand (normalize I) x (horizon (normalize I)),
          ∀ σ, Compat (normalize I) (key (normalize I) x β) σ →
            ∀ C : I.N → ℝ, IsFeasible I C →
              cost I (outSched I σ) ≤ 2 * (delta I : ℝ) * cost I C) ∧
    (∀ I : Instance, Acyclic I → ∀ ε : ℝ, 0 < ε →
      (∃ x, LP5Optimal (normalize I) (ε / (2 * (delta (normalize I) : ℝ))) x) ∧
      ∀ x, LP5Optimal (normalize I) (ε / (2 * (delta (normalize I) : ℝ))) x →
        (∀ β : ℝ, 0 < β → β ≤ 1 →
          (∃ σ, Compat (normalize I) (key (normalize I) x β) σ) ∧
          ∀ σ, Compat (normalize I) (key (normalize I) x β) σ → IsFeasible I (outSched I σ)) ∧
        (∀ β ∈ cand (normalize I) x (numIntervals (normalize I) (ε / (2 * (delta (normalize I) : ℝ)))),
          0 < β ∧ β ≤ 1) ∧
        Fintype.card (normalize I).N ≤ 2 * Fintype.card I.N ∧
        (cand (normalize I) x (numIntervals (normalize I) (ε / (2 * (delta (normalize I) : ℝ))))).card ≤
          Fintype.card (normalize I).N *
            numIntervals (normalize I) (ε / (2 * (delta (normalize I) : ℝ))) + 1 ∧
        (1 ≤ horizon (normalize I) →
          (numIntervals (normalize I) (ε / (2 * (delta (normalize I) : ℝ))) : ℝ) ≤
            2 + (1 + ε / (2 * (delta (normalize I) : ℝ))) * Real.log (horizon (normalize I)) /
              (ε / (2 * (delta (normalize I) : ℝ)))) ∧
        ∃ β ∈ cand (normalize I) x (numIntervals (normalize I) (ε / (2 * (delta (normalize I) : ℝ)))),
          ∀ σ, Compat (normalize I) (key (normalize I) x β) σ →
            ∀ C : I.N → ℝ, IsFeasible I C →
              cost I (outSched I σ) ≤ (2 * (delta I : ℝ) + ε) * cost I C) := by sorry

end AndOrSched
