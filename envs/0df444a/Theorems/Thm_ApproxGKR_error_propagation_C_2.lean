-- Prove2me | Theorems.Thm_ApproxGKR_error_propagation_C_2
-- name    : ApproxGKR.error_propagation_C_2
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T11:28:00.542539+00:00
-- url     : https://prove2.me/theorems/ca9ee56d-5a13-48e2-8120-9ce48c1ebb8f
-- title:
--   §C.2 — error propagation in a numerical computation of bounded depth
-- statement:
--   Model a numerical computation as a directed acyclic graph on nodes $0,\dots,n-1$ whose operation nodes ($+,-,\times$) use earlier nodes. Let $x_v$ be the exact values ($x_v=x_l\circ x_r$ at an operation node), all of modulus at most $B\ge1$, and let $\tilde x_v$ be computed values with
--   - $|\tilde x_v-x_v|\le e_{\mathrm{op}}$ at input nodes, and
--   - $|\tilde x_v-(\tilde x_l\circ\tilde x_r)|\le e_{\mathrm{op}}$ at operation nodes,
--
--   where $e_{\mathrm{op}}\ge0$. If $e_{\mathrm{op}}(2B+3)^{\mathrm{depth}(v)}\le1$ at every node, then at every node
--   $$|\tilde x_v-x_v|\le e_{\mathrm{op}}(2B+3)^{\mathrm{depth}(v)}.$$
--
--   This bound determines the working precision of both parties.
--
--   Differences from the source:
--   - generalization: output error of a computation of depth d → the bound at every node, with that node's depth; reason: each node is the output of the computation below it; the output is a node
--   - reading: "provided this quantity is at most one" for the computation's depth → e_op(2B + 3)^{depth(v)} ≤ 1 at every node; reason: equivalent: the maximum depth is d and the bound is monotone in the depth
--   - encoding: a directed acyclic graph of arithmetic operations → nodes indexed by ℕ, operations +, −, × on earlier nodes, constants as inputs; reason: the page's model; subtraction behaves as addition
-- source:
--   Das, Gupta, Mondal, More, Delegating Computation with Approximate Arithmetic: Interactive Proofs for Wizards (manuscript, sha256 78b2a36b…), §C.2, pp.34–35

import Mathlib
import Definitions.Def_ApproxGKR_DagNode

namespace ApproxGKR

/-- **Error propagation in a numerical computation** (§C.2, pp.34–35).

Das, Gupta, Mondal, More, *Delegating Computation with Approximate Arithmetic* (manuscript,
sha256 78b2a36b…), §C.2, pp.34–35: "Model each numerical computation as a directed acyclic graph
of arithmetic operations, with depth at most `dnum` and exact intermediate values of modulus at
most `Bnum ≥ 1`." "If each input approximation and arithmetic operation introduces absolute error
at most `eop`, a computation of depth `d` has output error at most `eop(2Bnum + 3)^d`, provided
this quantity is at most one."

Let `G` be a DAG on the nodes `0, …, n−1` (operations only on earlier nodes) with exact values
`x_v` (`x_v = op(x_l, x_r)` at operation nodes) of modulus at most `B ≥ 1`, and computed values
`x̃_v` with `|x̃_v − x_v| ≤ e_op` at inputs and `|x̃_v − op(x̃_l, x̃_r)| ≤ e_op` at operations. If
`e_op(2B + 3)^{depth(v)} ≤ 1` at every node, then `|x̃_v − x_v| ≤ e_op(2B + 3)^{depth(v)}` at every
node.

**Formalization Note** Operations are `+`, `−`, `×`; constants, approximate roots and supplied
oracle evaluations are input nodes, as on the page. The proviso at every node is the proviso at
the computation's depth `d = max_v depth(v)`. -/
theorem error_propagation_C_2 (G : ℕ → DagNode) (n : ℕ) (x xt : ℕ → ℂ) (B eop : ℝ)
    (hwf : ∀ v < n, ∀ o l r, G v = DagNode.op o l r → l < v ∧ r < v)
    (hx : ∀ v < n, ∀ o l r, G v = DagNode.op o l r → x v = o.eval (x l) (x r))
    (hB : 1 ≤ B) (hxB : ∀ v < n, ‖x v‖ ≤ B) (heop : 0 ≤ eop)
    (hin : ∀ v < n, G v = DagNode.input → ‖xt v - x v‖ ≤ eop)
    (hop : ∀ v < n, ∀ o l r, G v = DagNode.op o l r → ‖xt v - o.eval (xt l) (xt r)‖ ≤ eop)
    (hsmall : ∀ v < n, eop * (2 * B + 3) ^ (dagDepth G v) ≤ 1) :
    ∀ v < n, ‖xt v - x v‖ ≤ eop * (2 * B + 3) ^ (dagDepth G v) := by sorry

end ApproxGKR
