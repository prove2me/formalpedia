-- Prove2me | Theorems.Thm_CancelFreeHessian_Formula_eq_4
-- name    : CancelFreeHessian.Formula.eq_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:58:06.386813+00:00
-- url     : https://prove2.me/theorems/28ae12f0-8a89-42ac-99a3-93924223ac75
-- title:
--   §4, Eq. (4) — summation at branching nodes: ∂²f/∂x_i² = Σ_{ℓ∈L_i} b(ℓ) + 2 Σ_{w∈B_i} K(w) D_i(c_w) D_i(c′_w), with D_i(c) = ∂c/∂x_i
-- statement:
--   Let $f$ be computed by a scalar formula whose output is an operation gate, with $C^2$ local functions. Fix a point $x$, take the leaf variables $y_\ell=x_{\mathrm{var}(\ell)}$, and an input $x_i$. For a node $c$ put $D_i(c)=\sum_{\ell\in L_i\text{ below }c}d(c,\ell)$; it equals $\partial c/\partial x_i$. Let $B_i$ be the set of operation gates $w$ with leaves of $L_i$ below both children $c_w$ (slot 1) and $c'_w$ (slot 2). Then
--   $$\frac{\partial^2 f}{\partial x_i^2}(x)=\sum_{\ell\in L_i}b(\ell)+2\sum_{w\in B_i}K(w)\,D_i(c_w)\,D_i(c'_w).$$
--   This is the form of the diagonal that the algorithm of Theorem 3 evaluates.
--
--   Differences from the source:
--   - encoding: a DAG of gates with ordered slots 1, 2 → gates numbered 0, …, s − 1 in a topological order (`Dag n`, `WellFormed`), slots as `κ : Fin 2` (κ = 0 is slot 1); reason: every finite DAG has a topological numbering; no instance changes
--   - encoding: the tree unfolding T rooted at the output gate (implicitly an operation gate) → hypothesis `D.IsOp D.out`; reason: if the output is an input or constant gate, T has no node and g is undefined; this only excludes that degenerate case, where no input is active
--   - encoding: independent variables y_ℓ for input leaves ℓ → one real `y ℓ` for every slot pair `ℓ = (v, κ) : ℕ × Fin 2`; only input leaves are read; reason: unused coordinates do not change any value or derivative
--   - encoding: partial derivatives ∂/∂y_ℓ, ∂/∂x_i → `pd G j z` = derivative of `u ↦ G(z with z_j := u)` at `z_j`; second partials as `pd (pd G j) j′`; reason: the genuine partial derivatives; the functions are C² so no junk value of `deriv` is reached
--   - encoding: local partials φ_{v,κ}, φ_{v,κκ}, φ_{v,12} → `lp1 (φ v) κ`, `lp2 (φ v) κ`, `lp12 (φ v)` (∂₂∂₁) at the values of the two children; reason: one-variable derivatives of φ_v; for φ_v ∈ C² the mixed partial is symmetric
-- source:
--   Tianlang Chen, The Cancellation-Free Cost of Hessian Diagonals: Exact Counts, Formulas and Interfaces, STOC 2027 submission (manuscript sha256 de5c3ef4…), p. 11, §4, Eq. (4)

import Mathlib
import Definitions.Def_CancelFreeHessian_Formula_Graph
import Definitions.Def_CancelFreeHessian_Formula_Tree

namespace CancelFreeHessian.Formula

/-- **§4, Eq. (4)** (Chen, p. 11). For a scalar formula whose output is an operation gate, with
`C²` local functions, at every point `x` (leaf variables `y_ℓ = x_{var(ℓ)}`) and every input
`x_i`: `D_i(u) = ∂u/∂x_i` for every node `u`, and
`∂²f/∂x_i² = Σ_{ℓ ∈ L_i} b(ℓ) + 2 Σ_{w ∈ B_i} K(w) D_i(c_w) D_i(c'_w)`, where `c_w, c'_w` are the
slot-1 and slot-2 children of `w`. -/
theorem eq_4 (n : ℕ) (D : Dag n) (hD : D.IsScalarFormula) (hout : D.IsOp D.out)
    (c : ℕ → ℝ) (φ : ℕ → ℝ × ℝ → ℝ) (hφ : D.LocalC2 φ) (i : Fin n) (x : Fin n → ℝ) :
    (∀ u ∈ D.nodes,
        pd (fun x' => D.nodeVal c φ (D.leafPoint x') Dag.noOv u) i x =
          D.Dsum c φ (D.leafPoint x) i u) ∧
      hessDiag (D.fn c φ) i x =
        ∑ ℓ ∈ D.leavesOf i, D.adjB c φ (D.leafPoint x) (.leaf ℓ) +
          2 * ∑ w ∈ D.branching i,
            D.Kfac c φ (D.leafPoint x) w * D.Dsum c φ (D.leafPoint x) i (D.child w 0) *
              D.Dsum c φ (D.leafPoint x) i (D.child w 1) := by sorry

end CancelFreeHessian.Formula
