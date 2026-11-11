-- Prove2me | Theorems.Thm_CancelFreeHessian_Formula_eq_2
-- name    : CancelFreeHessian.Formula.eq_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:57:58.052771+00:00
-- url     : https://prove2.me/theorems/49cd5f2f-3c2b-4ae9-8270-a5f90f1171f4
-- title:
--   §4, Eq. (2) — adjoint recursion a(c) = a(v)φ_{v,κ}, b(c) = b(v)φ²_{v,κ} + a(v)φ_{v,κκ}
-- statement:
--   In the tree unfolding of a scalar formula whose output is an operation gate, with $C^2$ local functions, fix any values $y$ of the leaf variables. For each node $u$, holding every leaf outside the subtree of $u$ fixed, the root value is a $C^2$ function $F_u$ of the value at $u$; set $a(u)=F_u'$ and $b(u)=F_u''$ at the current value. Then $a(\mathrm{root})=1$, $b(\mathrm{root})=0$, and for the child $c$ of an operation gate $v$ in slot $\kappa$,
--   $$a(c)=a(v)\,\varphi_{v,\kappa},\qquad b(c)=b(v)\,\varphi_{v,\kappa}^2+a(v)\,\varphi_{v,\kappa\kappa},$$
--   the local partials taken at the current values of the children of $v$. This is the second-order reverse sweep of the proof of Theorem 3.
--
--   Differences from the source:
--   - encoding: a DAG of gates with ordered slots 1, 2 → gates numbered 0, …, s − 1 in a topological order (`Dag n`, `WellFormed`), slots as `κ : Fin 2` (κ = 0 is slot 1); reason: every finite DAG has a topological numbering; no instance changes
--   - encoding: the tree unfolding T rooted at the output gate (implicitly an operation gate) → hypothesis `D.IsOp D.out`; reason: if the output is an input or constant gate, T has no node and g is undefined; this only excludes that degenerate case, where no input is active
--   - encoding: independent variables y_ℓ for input leaves ℓ → one real `y ℓ` for every slot pair `ℓ = (v, κ) : ℕ × Fin 2`; only input leaves are read; reason: unused coordinates do not change any value or derivative
--   - encoding: local partials φ_{v,κ}, φ_{v,κκ}, φ_{v,12} → `lp1 (φ v) κ`, `lp2 (φ v) κ`, `lp12 (φ v)` (∂₂∂₁) at the values of the two children; reason: one-variable derivatives of φ_v; for φ_v ∈ C² the mixed partial is symmetric
--   - encoding: F_u: the root value as a function of the value at u, every leaf outside the subtree of u fixed → `Fnode c φ y u t`: the tree evaluated with the value of node u replaced by t; reason: replacing the value at u is exactly freezing everything outside the subtree of u
-- source:
--   Tianlang Chen, The Cancellation-Free Cost of Hessian Diagonals: Exact Counts, Formulas and Interfaces, STOC 2027 submission (manuscript sha256 de5c3ef4…), p. 11, §4, Eq. (2)

import Mathlib
import Definitions.Def_CancelFreeHessian_Formula_Graph
import Definitions.Def_CancelFreeHessian_Formula_Tree

namespace CancelFreeHessian.Formula

/-- **§4, Eq. (2)** (Chen, p. 11). For a scalar formula whose output is an operation gate, with
`C²` local functions, at any leaf variables `y`: every `F_u` is `C²`; `a(root) = 1`,
`b(root) = 0`; and for the child `c` of the operation gate `v` in slot `κ`,
`a(c) = a(v) φ_{v,κ}` and `b(c) = b(v) φ_{v,κ}² + a(v) φ_{v,κκ}`. -/
theorem eq_2 (n : ℕ) (D : Dag n) (hD : D.IsScalarFormula) (hout : D.IsOp D.out)
    (c : ℕ → ℝ) (φ : ℕ → ℝ × ℝ → ℝ) (hφ : D.LocalC2 φ) (y : ℕ × Fin 2 → ℝ) :
    (∀ u ∈ D.nodes, ContDiff ℝ 2 (D.Fnode c φ y u)) ∧
      D.adjA c φ y (.gate D.out) = 1 ∧ D.adjB c φ y (.gate D.out) = 0 ∧
      ∀ v < D.size, D.IsOp v → ∀ κ : Fin 2,
        D.adjA c φ y (D.child v κ) =
            D.adjA c φ y (.gate v) * lp1 (φ v) κ (D.childArgs c φ y v) ∧
        D.adjB c φ y (D.child v κ) =
            D.adjB c φ y (.gate v) * lp1 (φ v) κ (D.childArgs c φ y v) ^ 2 +
              D.adjA c φ y (.gate v) * lp2 (φ v) κ (D.childArgs c φ y v) := by sorry

end CancelFreeHessian.Formula
