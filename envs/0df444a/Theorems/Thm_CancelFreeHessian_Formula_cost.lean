-- Prove2me | Theorems.Thm_CancelFreeHessian_Formula_cost
-- name    : CancelFreeHessian.Formula.cost
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:59:56.82659+00:00
-- url     : https://prove2.me/theorems/72fa18fc-7547-42db-acd4-2b41dde0e004
-- title:
--   §4, Cost — Σ_i |V_i| = O(s), and offline ancestor-path products in O(sα(s)) semigroup operations and RAM time [Tar79]
-- statement:
--   Two claims of the cost paragraph of the proof of Theorem 3.
--
--   1. There are $O(s)$ factors $d(c_\kappa,v_\kappa)$: one absolute constant $C_0$ such that $\sum_i|V_i|\le C_0\,s$ for every scalar formula of size $s$ whose output is an operation gate.
--   2. Offline path products in a commutative semigroup [Tar79]: for every constant $K$ there are a constant $C$, a deterministic word-RAM program $P$ and a word width such that for every rooted tree with $N$ nodes and every list of $Q$ ancestor-path queries with $N+Q\le K s$, where $s\ge 1$, the run of $P$ on the tree and the queries halts within $C\,s\,\alpha(s)$ steps and outputs one product-only program with at most
--   $$C\,s\,\alpha(s)$$
--   semigroup operations which, in every commutative semigroup and under every labelling of the edges, returns every queried path product. The sequence of operations depends only on the tree and the queries. Here $\alpha$ is the inverse Ackermann function.
--
--   Differences from the source:
--   - reading: the Cost paragraph → its two quantitative claims: Σ_i |V_i| = O(s) and the [Tar79] path-product bound; reason: the O(s) count of recursion (2), the K(w) and the sums (4), (5) is the gate count of the goal's circuit (Theorem 3), not a separate statement
--   - generalization: O(s) path products on the tree T of the formula → every rooted tree and query list with N + Q ≤ K·s, any K; reason: T has at most 3s nodes and Σ_i |V_i| = O(s) queries, so this specializes to the paper's instance
--   - reading: O(·) and "the inverse Ackermann function" → explicit constants C₀, C quantified before the instance; `Algo2Lean.Ackermann.alpha`; reason: variant unspecified; α ≥ 1 so the bound is meaningful at s = 1
--   - reading: "RAM time" → a deterministic `CongruencyTU` program with words of width·(1 + log₂(2 + N + Q)) bits, halting with the encoded program as output; reason: the paper names no model; a word bound is needed for unit-cost time to be meaningful
--   - encoding: a tree with edge labels in a commutative semigroup → parent array numbered from the leaves up (root N − 1), edge named by its lower endpoint, semigroups in `Type`; reason: every rooted tree has such a numbering; a straight-line program over formal labels is universe-independent
--   - encoding: s, the size of a formula → any natural number s with `1 ≤ s`; reason: a formula has at least one gate; at s = 0 the bound C·0·α(0) = 0 would force the fixed program to halt at cost 0 on the empty tree, which no program that does work on other inputs can do
--   - encoding: a DAG of gates with ordered slots 1, 2 → gates numbered 0, …, s − 1 in a topological order (`Dag n`, `WellFormed`), slots as `κ : Fin 2` (κ = 0 is slot 1); reason: every finite DAG has a topological numbering; no instance changes
--   - encoding: the tree unfolding T rooted at the output gate (implicitly an operation gate) → hypothesis `D.IsOp D.out`; reason: if the output is an input or constant gate, T has no node and g is undefined; this only excludes that degenerate case, where no input is active
-- source:
--   Tianlang Chen, The Cancellation-Free Cost of Hessian Diagonals: Exact Counts, Formulas and Interfaces, STOC 2027 submission (manuscript sha256 de5c3ef4…), p. 12, §4, Cost

import Mathlib
import Definitions.Def_Algo2LeanLib_Ackermann
import Definitions.Def_CongruencyTU_Machine
import Definitions.Def_CancelFreeHessian_Formula_Graph
import Definitions.Def_CancelFreeHessian_Formula_Tree
import Definitions.Def_CancelFreeHessian_Formula_Circuit
import Definitions.Def_CancelFreeHessian_Formula_Machine
import Definitions.Def_CancelFreeHessian_Formula_PathProducts

namespace CancelFreeHessian.Formula

/-- **§4, Cost** (Chen, p. 12, after [Tar79]). (1) There are `O(s)` virtual-tree nodes in total:
one constant `C₀` with `Σ_i |V_i| ≤ C₀ s` for every scalar formula of size `s` whose output is an
operation gate. (2) Offline path products: for every constant `K` there are a constant `C`, a
deterministic word-RAM program `P` and a word width such that for every rooted tree and every
list of ancestor-path queries with (number of nodes) + (number of queries) `≤ K s`, `s ≥ 1` (the
size of a formula), the run of
`P` outputs, within `C s α(s)` steps, one product-only program with at most `C s α(s)`
semigroup operations, fixed by the tree and the queries, that returns every queried path product
in every commutative semigroup under every edge labelling. -/
theorem cost :
    (∃ C₀ : ℕ, ∀ (n : ℕ) (D : Dag n), D.IsScalarFormula → D.IsOp D.out →
        ∑ i : Fin n, (D.vnodes i).card ≤ C₀ * D.size) ∧
      ∀ K : ℕ, ∃ (C : ℕ) (P : CongruencyTU.Program) (width : ℕ), Deterministic P ∧
        ∀ (s : ℕ) (T : RTree) (Qs : List (ℕ × ℕ)), 1 ≤ s → T.WF →
          (∀ q ∈ Qs, T.StrictAnc q.1 q.2) → T.N + Qs.length ≤ K * s →
          ∃ S : SProgram,
            S.size ≤ C * s * Algo2Lean.Ackermann.alpha s ∧
            S.Computes T Qs ∧
            WordBounded P (encPathInput T Qs) width (T.N + Qs.length) ∧
            HaltsWithOutput P (encPathInput T Qs) (C * s * Algo2Lean.Ackermann.alpha s)
              (encSProgram S) := by sorry

end CancelFreeHessian.Formula
