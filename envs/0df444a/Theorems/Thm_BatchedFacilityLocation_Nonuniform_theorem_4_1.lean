-- Prove2me | Theorems.Thm_BatchedFacilityLocation_Nonuniform_theorem_4_1
-- name    : BatchedFacilityLocation.Nonuniform.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:18:29.480428+00:00
-- url     : https://prove2.me/theorems/f42bb285-a186-4021-a408-f42412a9f17f
-- title:
--   Theorem 4.1 — nonuniform opening costs: O(min{log(B+1), √log(n−B+2)})-competitive
-- statement:
--   There are absolute constants $C_1,C_2>0$ such that the following holds. Let $(S,d)$ be a finite metric space of permitted sites with positive opening costs $f$, and consider any instance of $n\ge1$ clients located at sites, partitioned into $1\le B\le n$ nonempty batches that arrive in uniformly random order. The two-copy marginal Meyerson algorithm $\mathrm{ALG}_{\mathrm{comb}}$ (singleton batches to one copy, nonsingleton batches to another, each batch shuffled uniformly and processed client by client by the rule (4.2)) satisfies, for every comparison solution $a$,
--   $$\mathbb E[\mathrm{ALG}_{\mathrm{comb}}]\;\le\;C_1\,\mathrm{conn}(a)+C_2\min\Big\{\log(B+1),\sqrt{\log(n-B+2)}\Big\}\,\mathrm{open}(a).$$
--   The constants do not depend on $S$, $d$, $f$, the number of cost levels, $n$, $B$ or the instance.
--
--   This is the upper bound of the paper's tight $\Theta(\min\{\log(B+1),\sqrt{\log(n-B+2)}\})$ competitive ratio for nonuniform opening costs.
--
--   Differences from the source:
--   - generalization: there exists an algorithm → the explicit two-copy marginal Meyerson algorithm combAlg; reason: it is the paper's algorithm (proof, p. 24) and is online by construction; an existential over unconstrained algorithms would be trivial
--   - generalization: OPT_conn, OPT_open → conn(a), open(a) for every comparison solution a; reason: the optimal solution is a special case
--   - generalization: ALG_comb opens the union of the copies' facilities → ALG_comb is the sum of the two copies' costs; reason: the union version costs at most the sum
--   - generalization: a fixed distance tie-breaking rule → an arbitrary tie-breaking rule tb (any choice of a closest point); reason: the result holds for every fixed rule; the source's rule is one instance
--   - reading: permitted sites with a metric, known in advance → a finite metric space S of sites (Fintype S, MetricSpace S); reason: the algorithm needs finitely many rounded levels f_1 < ... < f_m and attained minima d(v, M_j); with infinitely many levels (4.1) is undefined
--   - encoding: O(1) and O(min{log(B + 1), √log(n − B + 2)}) → absolute constants C₁, C₂ > 0 quantified before the sites, costs, instance and solution; natural logarithm; n − B as a natural number (B ≤ n); reason: standard reading of O(·) with uniform constants
--   - encoding: uniform batch order and in-batch shuffles → average over the B! batch orders of the batch sequence; each batch averaged over its |l|! arrangements; lotteries i.i.d. uniform on [0,1]; reason: same law
--   - encoding: real-valued expectations and costs, d(v, empty set) = infinity → values in [0, infinity] (ENNReal lower integrals, ENNReal.ofReal of real costs); reason: all quantities are nonnegative; avoids the Bochner integral of a non-integrable function
--   - encoding: levels j = 1..m with rounded costs f_1 < ... < f_m; j <= j_C → a level is identified with its rounded cost t = f_j (subtype of the finite set of values of f-hat); j <= j_C is t <= f-hat(c); d_v^(j-1) = d(v, {y : f-hat(y) < f_j}); reason: the levels are exactly the distinct values of f-hat; same objects
-- source:
--   Fabrizio Grandoni, Stefano Leonardi, Matteo Russo, Metric Facility Location under Batched Random Order, STOC 2027 submission #212 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/212.pdf (source.pdf sha256 2e976c4133df9baa0c32b4cd22b6e370c2c4611dfe4d4dec02ceb01bd7a0dc94), Theorem 4.1, p. 13 (proof p. 13–24)

import Mathlib
import Definitions.Def_BatchedFacilityLocation_Nonuniform_Batched

open MeasureTheory
open scoped ENNReal NNReal

namespace BatchedFacilityLocation.Nonuniform

universe u

/-- Theorem 4.1 (Nonuniform opening costs, p. 13). There are absolute constants `C₁, C₂ > 0`
such that for every finite metric space of permitted sites with positive opening costs, every
instance of `n ≥ 1` clients in `1 ≤ B ≤ n` nonempty batches, and every comparison solution `a`,
the two-copy marginal Meyerson algorithm satisfies
`E[ALG_comb] ≤ C₁ conn(a) + C₂ min {log (B + 1), √(log (n - B + 2))} open(a)`. -/
theorem theorem_4_1 :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ (S : Type u) [Fintype S] [MetricSpace S] (tb : TieBreak S) (f : S → ℝ),
        (∀ y, 0 < f y) → ∀ I : Instance S, I.Valid → ∀ a : Fin I.n → S,
          brExp (combAlg tb f) I ≤
            ENNReal.ofReal (C₁ * connCost I.loc a +
              C₂ * min (Real.log (I.B + 1)) (Real.sqrt (Real.log (((I.n - I.B : ℕ) : ℝ) + 2))) *
                openCost f a) := by sorry

end BatchedFacilityLocation.Nonuniform
