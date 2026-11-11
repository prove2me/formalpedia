-- Prove2me | Theorems.Thm_CancelFreeHessian_Formula_eq_5
-- name    : CancelFreeHessian.Formula.eq_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:58:06.121381+00:00
-- url     : https://prove2.me/theorems/16f5d996-67fe-437a-acfa-ed0bd02ce61c
-- title:
--   §4, Eq. (5) — recursion D_i(c_κ) = d(c_κ, v_κ) D_i(v_κ), D_i(v) = φ_{v,1}D_i(c_1) + φ_{v,2}D_i(c_2) on the virtual tree
-- statement:
--   In the tree unfolding of a scalar formula whose output is an operation gate, at any values $y$ of the leaf variables and for an input $x_i$: $D_i(\ell)=1$ on the leaves $\ell\in L_i$; and for $v\in B_i$ with tree children $c_1,c_2$ (slots 1, 2) and $V_i$-children $v_1,v_2$ below them (possibly $c_\kappa=v_\kappa$), every leaf of $L_i$ below $c_\kappa$ lies below $v_\kappa$, and
--   $$D_i(c_\kappa)=d(c_\kappa,v_\kappa)\,D_i(v_\kappa),\qquad D_i(v)=\varphi_{v,1}D_i(c_1)+\varphi_{v,2}D_i(c_2).$$
--   With Eq. (4) this evaluates the diagonal over the virtual trees, given the path products $d(c_\kappa,v_\kappa)$.
--
--   Differences from the source:
--   - encoding: a DAG of gates with ordered slots 1, 2 → gates numbered 0, …, s − 1 in a topological order (`Dag n`, `WellFormed`), slots as `κ : Fin 2` (κ = 0 is slot 1); reason: every finite DAG has a topological numbering; no instance changes
--   - encoding: the tree unfolding T rooted at the output gate (implicitly an operation gate) → hypothesis `D.IsOp D.out`; reason: if the output is an input or constant gate, T has no node and g is undefined; this only excludes that degenerate case, where no input is active
--   - encoding: independent variables y_ℓ for input leaves ℓ → one real `y ℓ` for every slot pair `ℓ = (v, κ) : ℕ × Fin 2`; only input leaves are read; reason: unused coordinates do not change any value or derivative
--   - encoding: local partials φ_{v,κ}, φ_{v,κκ}, φ_{v,12} → `lp1 (φ v) κ`, `lp2 (φ v) κ`, `lp12 (φ v)` (∂₂∂₁) at the values of the two children; reason: one-variable derivatives of φ_v; for φ_v ∈ C² the mixed partial is symmetric
--   - generalization: local functions φ_v ∈ C²(ℝ²) (§3 standing assumption) → no smoothness hypothesis on `φ`; reason: (5) is an identity between sums of products of the numbers φ_{v,κ}, d and D_i, and needs no differentiability; it specializes to C² local functions
-- source:
--   Tianlang Chen, The Cancellation-Free Cost of Hessian Diagonals: Exact Counts, Formulas and Interfaces, STOC 2027 submission (manuscript sha256 de5c3ef4…), p. 12, §4, Eq. (5)

import Mathlib
import Definitions.Def_CancelFreeHessian_Formula_Graph
import Definitions.Def_CancelFreeHessian_Formula_Tree

namespace CancelFreeHessian.Formula

/-- **§4, Eq. (5)** (Chen, p. 12). For a scalar formula whose output is an operation gate, at any
leaf variables `y` and for an input `x_i`: `D_i(ℓ) = 1` on the leaves of `L_i`; and for `v ∈ B_i`
with tree children `c_1, c_2` (slots 1, 2) and `V_i`-children `v_1, v_2` below them, every leaf of
`L_i` below `c_κ` lies below `v_κ`, `D_i(c_κ) = d(c_κ, v_κ) D_i(v_κ)` and
`D_i(v) = φ_{v,1} D_i(c_1) + φ_{v,2} D_i(c_2)`. -/
theorem eq_5 (n : ℕ) (D : Dag n) (hD : D.IsScalarFormula) (hout : D.IsOp D.out)
    (c : ℕ → ℝ) (φ : ℕ → ℝ × ℝ → ℝ) (y : ℕ × Fin 2 → ℝ) (i : Fin n) :
    (∀ ℓ ∈ D.leavesOf i, D.Dsum c φ y i (.leaf ℓ) = 1) ∧
      ∀ v ∈ D.branching i, ∀ v₁ v₂ : Node, D.VChild i v 0 v₁ → D.VChild i v 1 v₂ →
        (∀ ℓ ∈ D.leavesOf i, D.Below (.leaf ℓ) (D.child v 0) → D.Below (.leaf ℓ) v₁) ∧
        (∀ ℓ ∈ D.leavesOf i, D.Below (.leaf ℓ) (D.child v 1) → D.Below (.leaf ℓ) v₂) ∧
        D.Dsum c φ y i (D.child v 0) = D.dpath c φ y (D.child v 0) v₁ * D.Dsum c φ y i v₁ ∧
        D.Dsum c φ y i (D.child v 1) = D.dpath c φ y (D.child v 1) v₂ * D.Dsum c φ y i v₂ ∧
        D.Dsum c φ y i (.gate v) =
          lp1 (φ v) 0 (D.childArgs c φ y v) * D.Dsum c φ y i (D.child v 0) +
            lp1 (φ v) 1 (D.childArgs c φ y v) * D.Dsum c φ y i (D.child v 1) := by sorry

end CancelFreeHessian.Formula
