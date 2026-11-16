-- Prove2me | Theorems.Thm_ARGFContract_Hardness_Supplement_theorem_9
-- name    : ARGFContract.Hardness.Supplement.theorem_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:06:36.090784+00:00
-- url     : https://prove2.me/theorems/bfd58c52-d386-4fa5-9f7c-c0882d3f00d7
-- title:
--   Theorem 9 (companion theorem; not used in the proof of the goal) — Algorithm 7 on Lipschitz competency clusters (corrected: O(N log N) at K = 1)
-- statement:
--   Let $f$ be an ARGF on agents $E=\{1,\dots,N\}$ with costs $c_i\ge0$ that satisfies Assumption B.1 with constant $L\ge0$, and let $C_1,\dots,C_K$ be given disjoint competency clusters covering $E$, of sizes $n_a$, with gaps $\epsilon_a\ge0$ ($|p_i-p_j|\le\epsilon_a$ for $i,j\in C_a$). Run Algorithm 7 with the clusters as classes: for every count vector $x$, $0\le x_a\le n_a$, it evaluates the cheapest set $S(x)$ with these cluster counts once and returns a best one, $S_{alg}$.
--
--   There is one program which, given the costs and the cluster labels, queries $f$ exactly once on each set $S(x)$ and returns such an $S_{alg}$; for every optimal $S_{OPT}$ with cluster profile $x^\star_a=|S_{OPT}\cap C_a|$,
--
--   $$\mu(S_{alg})\ \ge\ \mu(S_{OPT})-L\sum_{a=1}^K x^\star_a\epsilon_a\ \ge\ \mu(S_{OPT})-L\sum_{a=1}^K n_a\epsilon_a ,$$
--
--   and if $\epsilon_a=0$ for all $a$ then $S_{alg}$ is optimal. For every fixed $K$ there is a constant $C$ such that, up to the cost of oracle evaluations, the program executes at most
--
--   $$C\Big((N+1)^K+(N+1)\big(\lfloor\log_2(N+1)\rfloor+1\big)\Big)$$
--
--   instructions: $O(N^K)$ for $K\ge2$ and $O(N\log N)$ for $K=1$.
--
--   The theorem shows that approximately equal competencies, combined with a quantitative Lipschitz link between competency and value, give an additive approximation that degrades linearly in the cluster widths.
--
--   **Formalization Note** Running time is measured in the value-oracle real RAM of `OracleMachine` with oracle time zero. The program does not receive $p$, $L$ or the gaps. The source states $O(N^K)$ also at $K=1$; this is false for Algorithm 7 (see the correction below).
--
--   Differences from the source:
--   - encoding: running time of an offline algorithm with value oracle f (Definition 2.1(3): an evaluation costs O(|S|^{K_f})) → one uniform admissible program of the value-oracle real RAM (published SmaleNinth core plus integer memory, one-agent committee edits and a query instruction); time = executed instructions plus the oracle time τ(|S|) of every query; reason: unit-cost real arithmetic and comparisons with no sort, maximum or set-scan primitive; the oracle is charged per query as in Definition 2.1(3)
--   - correction: time O(N^K) up to oracle evaluations, including K = 1 → C·((N+1)^K + (N+1)(⌊log₂(N+1)⌋+1)) steps: O(N^K) for K ≥ 2, O(N log N) for K = 1; reason: counterexample at K = 1: f ≡ 0 (an ARGF with L = 0), one class, pairwise distinct costs. Algorithm 7 queries all N+1 cheapest prefixes, whose collection determines the sorted order of the costs; cost data reach control flow only through binary real comparisons, so the N! orders need N! distinct runs and some run executes at least log₂ N! = Θ(N log N) comparisons, which is not O(N)
--   - encoding: up to the cost of oracle evaluations of f → oracle time τ = 0, each query one step; reason: excludes exactly the evaluation cost of f
--   - encoding: Algorithm 7: enumerate every count vector, one oracle call on S(x) each, keep the best → the query trace has length ∏_a(n_a+1) and its sets are exactly {S(x) : x a profile}; the output is S(x) for a profile maximizing µ(S(·)); reason: this is the procedure the theorem names; cost ties broken by agent index
--   - generalization: a partition into clusters C_1,…,C_K → a labelling cl : Fin N → Fin K whose clusters may be empty; reason: an empty cluster has n_a = 0 and contributes a factor 1 to the profile count; partitions are a special case
--   - encoding: S_OPT, an optimal committee → every set Sopt with IsOptimalSet f c Sopt; reason: the bound is asserted for every maximizer, in particular the one the source names
--   - encoding: O(N^K) for fixed K → ∀ K ∃ C with base N+1; reason: (N+1)^K ≤ 2^K N^K for N ≥ 1 and K is fixed
--   - generalization: E is the pruned ground set returned by Algorithm 1 (p. 10, 'throughout the remainder of the paper') → no pruning hypothesis (p_i − c_i > 0 is not assumed); reason: the statement holds on every ground set; the pruned instances are a special case
-- source:
--   Jalal Etesami, Larkin Liu, Rilind Sahitaj, STOC 2027 submission #348 (October 2026), Theorem 9, p. 41 (proof p. 42)

import Mathlib
import Definitions.Def_ARGFContract_Hardness_ARGF
import Definitions.Def_ARGFContract_Hardness_Supplement_Prefixes
import Definitions.Def_ARGFContract_Hardness_Supplement_OracleMachine

open Finset

namespace ARGFContract.Hardness.Supplement

/-- Theorem 9, pp. 41–42 (Algorithm 7 on approximate clusters), with the runtime corrected at
`K = 1`. One uniform program, given costs and the labels of the clusters `C_1,…,C_K`, queries
`f` exactly once on every cheapest-prefix set `S(x)` and returns a best one `S_alg`. If `f` is
an ARGF satisfying Assumption B.1 with constant `L` and the clusters have gaps `ε_a ≥ 0`, then
for every optimal `S_OPT` with profile `x⋆`,
`µ(S_alg) ≥ µ(S_OPT) − L ∑_a x⋆_a ε_a ≥ µ(S_OPT) − L ∑_a n_a ε_a`, and `S_alg` is optimal
when all `ε_a = 0`. The instruction count is at most
`C ((N+1)^K + (N+1)(⌊log₂(N+1)⌋+1))`, oracle evaluations aside. -/
theorem theorem_9 :
    ∃ P : OracleProgram, Admissible P ∧ ∀ K : ℕ, ∃ C : ℕ,
      ∀ (n : ℕ) (p c : Fin n → ℝ) (f : Finset (Fin n) → ℝ) (cl : Fin n → Fin K)
        (L : ℝ) (ε : Fin K → ℝ),
        ARGFContract.Hardness.IsARGF p f → (∀ i, 0 ≤ c i) →
        LipschitzCompetency L p f → (∀ a, 0 ≤ ε a) → HasCompetencyGaps p cl ε →
        RunsWithin P f (fun _ => 0)
          (initState n (encodeReals c p) (encodeInts K (fun i => (cl i : ℕ))))
          (C * ((n + 1) ^ K + (n + 1) * (Nat.log 2 (n + 1) + 1)))
          (fun S _ Q =>
            (∃ x ∈ profiles cl, S = cheapestProfileSet c cl x ∧
              ∀ y ∈ profiles cl,
                netUtilityReal f c (cheapestProfileSet c cl y) ≤ netUtilityReal f c S) ∧
            Q.length = ∏ a, ((block cl a).card + 1) ∧
            Q.toFinset = (profiles cl).image (cheapestProfileSet c cl) ∧
            (∀ Sopt : Finset (Fin n), IsOptimalSet f c Sopt →
              netUtilityReal f c Sopt -
                  L * ∑ a, ((blockProfile cl Sopt a : ℕ) : ℝ) * ε a ≤ netUtilityReal f c S ∧
              netUtilityReal f c Sopt - L * ∑ a, ((block cl a).card : ℝ) * ε a ≤
                netUtilityReal f c Sopt -
                  L * ∑ a, ((blockProfile cl Sopt a : ℕ) : ℝ) * ε a) ∧
            ((∀ a, ε a = 0) → IsOptimalSet f c S)) := by sorry

end ARGFContract.Hardness.Supplement
