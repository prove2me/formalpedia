-- Prove2me | Theorems.Thm_ARGFContract_Hardness_Supplement_theorem_8
-- name    : ARGFContract.Hardness.Supplement.theorem_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:05:12.171416+00:00
-- url     : https://prove2.me/theorems/f8ca0d9d-0d33-43e3-9050-0fabb337dae8
-- title:
--   Theorem 8 (companion theorem; not used in the proof of the goal) — Algorithm 7 is exact for K competency classes (corrected: O(N log N) at K = 1)
-- statement:
--   Let $f$ be an ARGF on agents $E=\{1,\dots,N\}$ with costs $c_i\ge0$, and suppose the competency vector $p$ takes exactly $K$ distinct values, with classes $C_1,\dots,C_K$ of sizes $n_a=|C_a|$. **Algorithm 7** sorts each class by non-decreasing cost (ties by index), and for every count vector $x$ with $0\le x_a\le n_a$ forms the cheapest set $S(x)$ with these class counts, evaluates $\mu(S(x))=f(S(x))-\sum_{i\in S(x)}c_i$ with one oracle call, and keeps the best.
--
--   There is one program which, given the costs and the class labels, queries $f$ exactly once on each of the $\prod_{a=1}^K(n_a+1)\le(N+1)^K$ sets $S(x)$, returns a best one, and that set maximizes $\mu$ over all $S\subseteq E$:
--
--   $$\mu(S_{alg})=\max_{S\subseteq E}\Big[f(S)-\sum_{i\in S}c_i\Big].$$
--
--   For every fixed $K$ there is a constant $C$ such that, up to the cost of the oracle evaluations, the program executes at most
--
--   $$C\Big((N+1)^K+(N+1)\big(\lfloor\log_2(N+1)\rfloor+1\big)\Big)$$
--
--   instructions, that is $O(N^K)$ for $K\ge2$ and $O(N\log N)$ for $K=1$.
--
--   Few distinct competency levels therefore make µ-Max exactly solvable in polynomial time, in contrast to the hardness of Theorem 1.
--
--   **Formalization Note** Running time is measured in the value-oracle real RAM of `OracleMachine` with oracle time zero (each query is one step). The source states $O(N^K)$ also at $K=1$; this is false for Algorithm 7 (see the correction below), so the bound carries the cost of sorting.
--
--   Differences from the source:
--   - encoding: running time of an offline algorithm with value oracle f (Definition 2.1(3): an evaluation costs O(|S|^{K_f})) → one uniform admissible program of the value-oracle real RAM (published SmaleNinth core plus integer memory, one-agent committee edits and a query instruction); time = executed instructions plus the oracle time τ(|S|) of every query; reason: unit-cost real arithmetic and comparisons with no sort, maximum or set-scan primitive; the oracle is charged per query as in Definition 2.1(3)
--   - correction: time O(N^K) up to oracle evaluations, including K = 1 → C·((N+1)^K + (N+1)(⌊log₂(N+1)⌋+1)) steps: O(N^K) for K ≥ 2, O(N log N) for K = 1; reason: counterexample at K = 1: f ≡ 0 (an ARGF with L = 0), one class, pairwise distinct costs. Algorithm 7 queries all N+1 cheapest prefixes, whose collection determines the sorted order of the costs; cost data reach control flow only through binary real comparisons, so the N! orders need N! distinct runs and some run executes at least log₂ N! = Θ(N log N) comparisons, which is not O(N)
--   - encoding: up to the cost of oracle evaluations of f → oracle time τ = 0, each query one step; reason: excludes exactly the evaluation cost of f
--   - encoding: Algorithm 7: enumerate every count vector, one oracle call on S(x) each, keep the best → the query trace has length ∏_a(n_a+1) and its sets are exactly {S(x) : x a profile}; the output is S(x) for a profile maximizing µ(S(·)); reason: this is the procedure the theorem names; cost ties broken by agent index
--   - encoding: p takes only K distinct values; Algorithm 7 receives the competency classes C_1,…,C_K → integer labels cls : Fin N → Fin K, surjective, with cls i = cls j ↔ p_i = p_j; reason: the classes are the fibres of p, supplied as Algorithm 7's input
--   - encoding: O(N^K) for fixed K → ∀ K ∃ C with base N+1; reason: (N+1)^K ≤ 2^K N^K for N ≥ 1 and K is fixed
--   - generalization: E is the pruned ground set returned by Algorithm 1 (p. 10, 'throughout the remainder of the paper') → no pruning hypothesis (p_i − c_i > 0 is not assumed); reason: the statement holds on every ground set; the pruned instances are a special case
-- source:
--   Jalal Etesami, Larkin Liu, Rilind Sahitaj, STOC 2027 submission #348 (October 2026), Theorem 8, pp. 38–39 (proof pp. 39–40)

import Mathlib
import Definitions.Def_ARGFContract_Hardness_ARGF
import Definitions.Def_ARGFContract_Hardness_Supplement_Prefixes
import Definitions.Def_ARGFContract_Hardness_Supplement_OracleMachine

open Finset

namespace ARGFContract.Hardness.Supplement

/-- Theorem 8, pp. 38–40 (Algorithm 7), with the runtime corrected at `K = 1`. One uniform
program, given costs and the labels of the `K` competency classes (the fibres of `p`),
queries `f` exactly once on every cheapest-prefix set `S(x)`, `0 ≤ x_a ≤ n_a`, returns a best
one, and that set is optimal for `µ`. For each fixed `K` it executes at most
`C ((N+1)^K + (N+1)(⌊log₂(N+1)⌋+1))` instructions, oracle evaluations aside (each query is one
step): `O(N^K)` for `K ≥ 2` and `O(N log N)` for `K = 1`. -/
theorem theorem_8 :
    ∃ P : OracleProgram, Admissible P ∧ ∀ K : ℕ, ∃ C : ℕ,
      ∀ (n : ℕ) (p c : Fin n → ℝ) (f : Finset (Fin n) → ℝ) (cls : Fin n → Fin K),
        ARGFContract.Hardness.IsARGF p f → (∀ i, 0 ≤ c i) →
        Function.Surjective cls → (∀ i j, cls i = cls j ↔ p i = p j) →
        RunsWithin P f (fun _ => 0)
          (initState n (encodeReals c p) (encodeInts K (fun i => (cls i : ℕ))))
          (C * ((n + 1) ^ K + (n + 1) * (Nat.log 2 (n + 1) + 1)))
          (fun S _ Q =>
            IsOptimalSet f c S ∧
            (∃ x ∈ profiles cls, S = cheapestProfileSet c cls x ∧
              ∀ y ∈ profiles cls,
                netUtilityReal f c (cheapestProfileSet c cls y) ≤ netUtilityReal f c S) ∧
            Q.length = ∏ a, ((block cls a).card + 1) ∧
            Q.toFinset = (profiles cls).image (cheapestProfileSet c cls)) := by sorry

end ARGFContract.Hardness.Supplement
