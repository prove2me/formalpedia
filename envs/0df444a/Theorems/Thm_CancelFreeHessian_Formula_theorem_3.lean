-- Prove2me | Theorems.Thm_CancelFreeHessian_Formula_theorem_3
-- name    : CancelFreeHessian.Formula.theorem_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:59:53.007217+00:00
-- url     : https://prove2.me/theorems/308380ff-9641-4bcb-b395-96da148db5cc
-- title:
--   Theorem 3 — Hessian diagonal of a scalar formula of size s in C·s·α(s) additions and multiplications, cancellation-free (opaque monotone circuit), no division, built in C·s·α(s) RAM time
-- statement:
--   Let $f$ be computed by a **scalar formula** of size $s$: a computation graph with $C^2$ local functions on two ordered slots in which no operation gate is used twice, while input variables may be repeated at any number of leaves. Then all $\partial^2 f/\partial x_i^2$ for active $i$ can be computed in $O(s\,\alpha(s))$ additions and multiplications, with an absolute constant, cancellation-free and with no division, where $\alpha$ is the inverse Ackermann function; the bookkeeping takes time of the same order on a RAM. Explicitly: there are an absolute constant $C$, a deterministic word-RAM program $P$ and a word width, fixed before the formula, such that for every scalar formula $D$ with $n$ inputs and $s$ gates, the run of $P$ on the encoding of $D$ halts within $C\,s\,\alpha(s)$ steps and outputs a monotone circuit $K$ (gates $+$ and $\times$; leaves the local symbols and natural-number constants) with
--   $$|K|\le C\,s\,\alpha(s)$$
--   gates such that, for every active $x_i$, the output of $K$ for $i$ equals $\partial^2 f/\partial x_i^2(x)$ whenever the symbols receive the local data of any evaluation: any $C^2$ local functions, any constant values, any point $x$.
--
--   The bound is within the factor $\alpha(s)$ of the cost of one evaluation of $f$, without subtraction or division.
--
--   Differences from the source:
--   - generalization: Definition 1: one monotone circuit per structure (DAG with slots and the symbolic form of the local functions), correct on the data of every evaluation → opaque: one circuit per DAG with slots (`∃ K` after `D`, before `c`, `φ`, `x`), correct for every C² local functions, constant values and point; reason: the paper states the algorithm of Theorem 3 is opaque; a circuit correct for all local functions is in particular correct for those of a given symbolic form
--   - generalization: leaves: formal symbols or nonnegative real constants → leaves: formal symbols or natural-number constants; reason: a circuit with natural constants is a monotone circuit of the paper, so the claim specializes; it lets the RAM output the circuit as integers
--   - reading: "the inverse Ackermann function" → `Algo2Lean.Ackermann.alpha` (α(n) = min{k > 0 : n < A_k(1)}); reason: variant unspecified; standard variants agree up to constant factors and the constant is existential; α ≥ 1
--   - reading: "The bookkeeping takes time of the same order on a RAM" → one deterministic `CongruencyTU` program P with a word width, fixed before the formula, halts on `encDag D` within C·s·α(s) cost with output `encCircuit K`, every register of bit length ≤ width·(1 + log₂(2 + n + s)); reason: the paper names no model; a word bound is needed for unit-cost time, and n enters because the input labels i < n are part of the input
--   - encoding: O(sα(s)) "with an absolute constant" → `∃ C : ℕ` before n and the formula, bounds `C * s * alpha s`; reason: one constant for all formulas, all s and all n
--   - encoding: a DAG of gates with ordered slots 1, 2 → gates numbered 0, …, s − 1 in a topological order (`Dag n`, `WellFormed`), slots as `κ : Fin 2` (κ = 0 is slot 1); reason: every finite DAG has a topological numbering; no instance changes
--   - encoding: input gates x_1, …, x_n; gates without a path to the output deleted → `InputsDistinct` (at most one gate per variable; variables without a gate allowed) and `InCone`; reason: after deletion an inactive variable may have no gate
--   - encoding: local data: value and local partials of each operation gate → `localData`: symbols of positions that are not operation gates receive 0; reason: such symbols are not local data; 0 is already a constant leaf
--   - encoding: the circuit and its outputs → straight-line program `Circuit` (size = number of + and × gates; an output may be a leaf), output for x_i = first pair (i, o) in `outs`; reason: a monotone circuit with several outputs
--   - encoding: partial derivatives ∂/∂y_ℓ, ∂/∂x_i → `pd G j z` = derivative of `u ↦ G(z with z_j := u)` at `z_j`; second partials as `pd (pd G j) j′`; reason: the genuine partial derivatives; the functions are C² so no junk value of `deriv` is reached
--   - encoding: local partials φ_{v,κ}, φ_{v,κκ}, φ_{v,12} → `lp1 (φ v) κ`, `lp2 (φ v) κ`, `lp12 (φ v)` (∂₂∂₁) at the values of the two children; reason: one-variable derivatives of φ_v; for φ_v ∈ C² the mixed partial is symmetric
-- source:
--   Tianlang Chen, The Cancellation-Free Cost of Hessian Diagonals: Exact Counts, Formulas and Interfaces, STOC 2027 submission (manuscript sha256 de5c3ef4…), p. 11, Theorem 3

import Mathlib
import Definitions.Def_Algo2LeanLib_Ackermann
import Definitions.Def_CongruencyTU_Machine
import Definitions.Def_CancelFreeHessian_Formula_Graph
import Definitions.Def_CancelFreeHessian_Formula_Circuit
import Definitions.Def_CancelFreeHessian_Formula_Machine

namespace CancelFreeHessian.Formula

/-- **Theorem 3** (Chen, p. 11). There are an absolute constant `C`, a deterministic word-RAM
program `P` and a word width, all fixed before the formula, such that for every scalar formula
`D` of size `s` (any number `n` of inputs, variables repeated at any number of leaves) the run of
`P` on the encoding of `D` halts within `C·s·α(s)` steps (logarithmic words) and outputs one
monotone circuit `K` (`+`, `×`, natural-number constants, no division) with at most `C·s·α(s)`
gates which, for every active input `x_i`, computes `∂²f/∂x_i²(x)` from the local data at every
evaluation (every `C²` local functions, every constant values, every point). -/
theorem theorem_3 :
    ∃ (C : ℕ) (P : CongruencyTU.Program) (width : ℕ), Deterministic P ∧
      ∀ (n : ℕ) (D : Dag n), D.IsScalarFormula →
        ∃ K : Circuit,
          K.size ≤ C * D.size * Algo2Lean.Ackermann.alpha D.size ∧
          ComputesHessianDiagonal D K ∧
          WordBounded P (encDag D) width (n + D.size) ∧
          HaltsWithOutput P (encDag D) (C * D.size * Algo2Lean.Ackermann.alpha D.size)
            (encCircuit K) := by sorry

end CancelFreeHessian.Formula
