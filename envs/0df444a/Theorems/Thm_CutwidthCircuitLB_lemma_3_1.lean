-- Prove2me | Theorems.Thm_CutwidthCircuitLB_lemma_3_1
-- name    : CutwidthCircuitLB.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:29:57.385586+00:00
-- url     : https://prove2.me/theorems/aca33579-b492-417f-aa81-56753a93cdc7
-- title:
--   Lemma 3.1 (Circuit Decomposition Lemma) — circuits of size $\le cn$ become unambiguous read-once programs of width $2^{(1-\delta)n}$
-- statement:
--   Suppose the cubic cutwidth constant is at most $\alpha$, and let $c < 1 + 1/\alpha$. Then there is a $\delta > 0$ such that, for all sufficiently large $n$, every non-degenerate $B_2$-circuit $C$ with $s \le cn$ gates on $n$ input variables has an equivalent unambiguous read-once program $R$ with
--   1. at most $2s + 1$ transition layers, and
--   2. width at most $2^{(1-\delta)n}$.
--
--   Consequently, $R$ has $O(n\, 2^{(1-\delta)n})$ edges: there is a constant $C_0$ (depending on $\alpha$ and $c$ only) with
--   $$
--   E(R) \le C_0\, n\, 2^{(1-\delta)n}.
--   $$
--
--   This is the compiler of the paper, the circuit half of the lower bound: small circuits become read-once programs with far fewer than $2^n$ edges.
--
--   **Formalization Note** "Equivalent" means that $R$ computes the function computed by $C$.
--
--   Differences from the source:
--   - encoding: c < 1 + 1/α (α implicitly positive) → hypotheses 0 < α and c < 1 + 1/α; reason: 1/α needs α ≠ 0, and the cutwidth hypothesis fails for α ≤ 0 (cubic graphs have linear cutwidth), so no instance with content is excluded
--   - reading: the cubic cutwidth constant (an infimum over admissible β > 0) is at most α → CubicCutwidthAtMost α: every β > α admits r = o(N) with cw ≤ β(M − N) + r(N); reason: the admissible set is upward closed (M − N ≥ −1 for connected graphs), so this is equivalent to the infimum being at most α; r(N) < o(N) read as r = o(N)
--   - reading: O(n 2^{(1−δ)n}) edges → numEdges ≤ C₀·n·2^{(1−δ)n} with C₀ chosen with δ before n; reason: the usual meaning of O(·), uniform in n
-- source:
--   McGuire–Schlesinger–Williams, Explicit functions requiring larger than 4.5n size circuits, STOC 2027 submission (manuscript sha256 ed87148f…cfa3), Lemma 3.1, p.8

import Mathlib
import Definitions.Def_CutwidthCircuitLB_B2Circuit
import Definitions.Def_CutwidthCircuitLB_B2Circuit_prefixValues
import Definitions.Def_CutwidthCircuitLB_B2Circuit_eval
import Definitions.Def_CutwidthCircuitLB_B2Circuit_IsRead
import Definitions.Def_CutwidthCircuitLB_B2Circuit_NonDegenerate
import Definitions.Def_CutwidthCircuitLB_ROBP
import Definitions.Def_CutwidthCircuitLB_ROBP_IsConsistentSegment
import Definitions.Def_CutwidthCircuitLB_ROBP_IsAcceptingPath
import Definitions.Def_CutwidthCircuitLB_ROBP_Accepts
import Definitions.Def_CutwidthCircuitLB_ROBP_Computes
import Definitions.Def_CutwidthCircuitLB_ROBP_Unambiguous
import Definitions.Def_CutwidthCircuitLB_ROBP_width
import Definitions.Def_CutwidthCircuitLB_ROBP_numEdges
import Definitions.Def_CombOpt_MatchingPolytope_Graph
import Definitions.Def_CombOpt_MatchingPolytope_Graph_IsLoopless
import Definitions.Def_CutwidthCircuitLB_IsSubcubic
import Definitions.Def_CutwidthCircuitLB_IsConnected
import Definitions.Def_CutwidthCircuitLB_edgeMultiset
import Definitions.Def_CutwidthCircuitLB_cutSize
import Definitions.Def_CutwidthCircuitLB_CutwidthLE
import Definitions.Def_CutwidthCircuitLB_CubicCutwidthAtMost

namespace CutwidthCircuitLB

/-- **Lemma 3.1 (Circuit Decomposition Lemma, Full Formal Statement)** (McGuire–Schlesinger–Williams, *Explicit functions requiring larger than 4.5n size circuits*, STOC 2027 submission manuscript (sha256 ed87148f…cfa3), Lemma 3.1, p.8):
suppose the cubic cutwidth constant is at most `α`, and let `c < 1 + 1/α`. Then there is a `δ > 0`
such that, for all sufficiently large `n`, every non-degenerate B₂-circuit with `s ≤ cn` gates on `n`
input variables has an equivalent unambiguous read-once program with at most `2s + 1` transition
layers and width at most `2^((1−δ)n)`; consequently this program has `O(n 2^((1−δ)n))` edges.

**Formalization Note** `0 < α` (the paper writes `1/α`; the constant is positive). "Equivalent"
is: the program computes the circuit's function. The `O(·)` is an explicit constant `C₀`, chosen
with `δ` before `n`. -/
theorem lemma_3_1 (α : ℝ) (hα : 0 < α) (hcw : CubicCutwidthAtMost α) (c : ℝ)
    (hc : c < 1 + 1 / α) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C₀ : ℝ, ∃ N : ℕ, ∀ n ≥ N, ∀ C : B2Circuit n, C.NonDegenerate →
      (C.size : ℝ) ≤ c * n →
        ∃ R : ROBP n, R.Computes C.eval ∧ R.Unambiguous ∧ R.len ≤ 2 * C.size + 1 ∧
          (R.width : ℝ) ≤ (2 : ℝ) ^ ((1 - δ) * n) ∧
          (R.numEdges : ℝ) ≤ C₀ * n * (2 : ℝ) ^ ((1 - δ) * n) := by sorry

end CutwidthCircuitLB
