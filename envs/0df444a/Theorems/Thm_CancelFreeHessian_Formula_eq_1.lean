-- Prove2me | Theorems.Thm_CancelFreeHessian_Formula_eq_1
-- name    : CancelFreeHessian.Formula.eq_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:57:51.250743+00:00
-- url     : https://prove2.me/theorems/e7e1e5f6-6334-4312-973a-a342f284328f
-- title:
--   §4, Eq. (1) — leaf-variable chain rule: ∂²f/∂x_i² = Σ_{ℓ,ℓ′∈L_i} ∂²g/∂y_ℓ∂y_ℓ′, with |T| ≤ 3s and f(x) = g(y)
-- statement:
--   Let $f$ be computed by a scalar formula of size $s$ whose output is an operation gate, with $C^2$ local functions and any constant values. Unfold it into its tree $T$, give each input leaf $\ell$ an independent variable $y_\ell$, and let $g(y)$ be the root value. Then $T$ has at most $3s$ nodes, $f(x)=g(y)$ at $y_\ell=x_{\mathrm{var}(\ell)}$, and for every input $x_i$ and every point $x$,
--   $$\frac{\partial^2 f}{\partial x_i^2}(x)=\sum_{\ell,\ell'\in L_i}\frac{\partial^2 g}{\partial y_\ell\,\partial y_{\ell'}}(y),\qquad y_\ell=x_{\mathrm{var}(\ell)},$$
--   where $L_i$ is the set of leaves labelled $x_i$. This reduces the Hessian diagonal of a formula with repeated variables to second partials of a read-once function of the leaf variables.
--
--   Differences from the source:
--   - encoding: a DAG of gates with ordered slots 1, 2 → gates numbered 0, …, s − 1 in a topological order (`Dag n`, `WellFormed`), slots as `κ : Fin 2` (κ = 0 is slot 1); reason: every finite DAG has a topological numbering; no instance changes
--   - encoding: the tree unfolding T rooted at the output gate (implicitly an operation gate) → hypothesis `D.IsOp D.out`; reason: if the output is an input or constant gate, T has no node and g is undefined; this only excludes that degenerate case, where no input is active
--   - encoding: independent variables y_ℓ for input leaves ℓ → one real `y ℓ` for every slot pair `ℓ = (v, κ) : ℕ × Fin 2`; only input leaves are read; reason: unused coordinates do not change any value or derivative
--   - encoding: partial derivatives ∂/∂y_ℓ, ∂/∂x_i → `pd G j z` = derivative of `u ↦ G(z with z_j := u)` at `z_j`; second partials as `pd (pd G j) j′`; reason: the genuine partial derivatives; the functions are C² so no junk value of `deriv` is reached
-- source:
--   Tianlang Chen, The Cancellation-Free Cost of Hessian Diagonals: Exact Counts, Formulas and Interfaces, STOC 2027 submission (manuscript sha256 de5c3ef4…), p. 11, §4, Eq. (1)

import Mathlib
import Definitions.Def_CancelFreeHessian_Formula_Graph
import Definitions.Def_CancelFreeHessian_Formula_Tree

namespace CancelFreeHessian.Formula

/-- **§4, Eq. (1)** (Chen, p. 11). For a scalar formula whose output is an operation gate, with
`C²` local functions: the tree unfolding has at most `3s` nodes; `f(x) = g(y)` with
`y_ℓ = x_{var(ℓ)}`; and for every input `x_i` and point `x`,
`∂²f/∂x_i² = Σ_{ℓ, ℓ' ∈ L_i} ∂²g/∂y_ℓ ∂y_ℓ'` at `y_ℓ = x_{var(ℓ)}`. -/
theorem eq_1 (n : ℕ) (D : Dag n) (hD : D.IsScalarFormula) (hout : D.IsOp D.out)
    (c : ℕ → ℝ) (φ : ℕ → ℝ × ℝ → ℝ) (hφ : D.LocalC2 φ) :
    D.nodes.card ≤ 3 * D.size ∧
      (∀ x : Fin n → ℝ, D.fn c φ x = D.gfun c φ (D.leafPoint x)) ∧
      ∀ (i : Fin n) (x : Fin n → ℝ),
        hessDiag (D.fn c φ) i x =
          ∑ ℓ ∈ D.leavesOf i, ∑ ℓ' ∈ D.leavesOf i,
            pd (pd (D.gfun c φ) ℓ) ℓ' (D.leafPoint x) := by sorry

end CancelFreeHessian.Formula
