-- Prove2me | Theorems.Thm_CancelFreeHessian_Formula_eq_3
-- name    : CancelFreeHessian.Formula.eq_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:57:55.518621+00:00
-- url     : https://prove2.me/theorems/ccd0c1a1-2fc9-498b-9faf-0f6bebd082ae
-- title:
--   §4, Eq. (3) — pair identity ∂²g/∂y_ℓ∂y_ℓ′ = K(w) d(c,ℓ) d(c′,ℓ′) at the lowest common ancestor, ∂²g/∂y_ℓ² = b(ℓ), d(u,ℓ) = ∂u/∂y_ℓ
-- statement:
--   In the tree unfolding of a scalar formula whose output is an operation gate, with $C^2$ local functions, at any values $y$ of the leaf variables, and for input leaves $\ell,\ell'$:
--
--   1. for every node $u$ above $\ell$, $d(u,\ell)=\partial u/\partial y_\ell$, where $d(u,\ell)$ is the product of local first partials on the path from $\ell$ up to $u$;
--   2. $\partial^2 g/\partial y_\ell^2=b(\ell)$;
--   3. if $\ell$ lies below the slot-1 child $c$ and $\ell'$ below the slot-2 child $c'$ of an operation gate $w$ (so $\ell\ne\ell'$ and $w$ is their lowest common ancestor), then
--   $$\frac{\partial^2 g}{\partial y_\ell\,\partial y_{\ell'}}=K(w)\,d(c,\ell)\,d(c',\ell'),\qquad K(w)=b(w)\varphi_{w,1}\varphi_{w,2}+a(w)\varphi_{w,12}.$$
--
--   Differences from the source:
--   - encoding: a DAG of gates with ordered slots 1, 2 → gates numbered 0, …, s − 1 in a topological order (`Dag n`, `WellFormed`), slots as `κ : Fin 2` (κ = 0 is slot 1); reason: every finite DAG has a topological numbering; no instance changes
--   - encoding: the tree unfolding T rooted at the output gate (implicitly an operation gate) → hypothesis `D.IsOp D.out`; reason: if the output is an input or constant gate, T has no node and g is undefined; this only excludes that degenerate case, where no input is active
--   - encoding: independent variables y_ℓ for input leaves ℓ → one real `y ℓ` for every slot pair `ℓ = (v, κ) : ℕ × Fin 2`; only input leaves are read; reason: unused coordinates do not change any value or derivative
--   - encoding: partial derivatives ∂/∂y_ℓ, ∂/∂x_i → `pd G j z` = derivative of `u ↦ G(z with z_j := u)` at `z_j`; second partials as `pd (pd G j) j′`; reason: the genuine partial derivatives; the functions are C² so no junk value of `deriv` is reached
--   - encoding: local partials φ_{v,κ}, φ_{v,κκ}, φ_{v,12} → `lp1 (φ v) κ`, `lp2 (φ v) κ`, `lp12 (φ v)` (∂₂∂₁) at the values of the two children; reason: one-variable derivatives of φ_v; for φ_v ∈ C² the mixed partial is symmetric
--   - encoding: "for ℓ ≠ ℓ′ with lowest common ancestor w, let c, c′ be the children of w above ℓ, ℓ′, in slots 1, 2" → hypotheses: ℓ below `child w 0` and ℓ′ below `child w 1`; reason: in a tree these say exactly that w is the lowest common ancestor and fix which leaf is under slot 1; the mixed partial is symmetric
-- source:
--   Tianlang Chen, The Cancellation-Free Cost of Hessian Diagonals: Exact Counts, Formulas and Interfaces, STOC 2027 submission (manuscript sha256 de5c3ef4…), p. 11, §4, Eq. (3)

import Mathlib
import Definitions.Def_CancelFreeHessian_Formula_Graph
import Definitions.Def_CancelFreeHessian_Formula_Tree

namespace CancelFreeHessian.Formula

/-- **§4, Eq. (3)** (Chen, p. 11). For a scalar formula whose output is an operation gate, with
`C²` local functions, at any leaf variables `y` and for input leaves: `d(u, ℓ) = ∂u/∂y_ℓ` for
every node `u` above `ℓ`; `∂²g/∂y_ℓ² = b(ℓ)`; and if `ℓ` lies below the slot-1 child `c` and `ℓ'`
below the slot-2 child `c'` of `w` (so `w` is their lowest common ancestor),
`∂²g/∂y_ℓ ∂y_ℓ' = K(w) d(c, ℓ) d(c', ℓ')` with `K(w) = b(w) φ_{w,1} φ_{w,2} + a(w) φ_{w,12}`. -/
theorem eq_3 (n : ℕ) (D : Dag n) (hD : D.IsScalarFormula) (hout : D.IsOp D.out)
    (c : ℕ → ℝ) (φ : ℕ → ℝ × ℝ → ℝ) (hφ : D.LocalC2 φ) (y : ℕ × Fin 2 → ℝ) :
    (∀ (i : Fin n), ∀ ℓ ∈ D.leavesOf i, ∀ u ∈ D.nodes, D.Below (.leaf ℓ) u →
        pd (fun y' => D.nodeVal c φ y' Dag.noOv u) ℓ y = D.dpath c φ y u (.leaf ℓ)) ∧
      (∀ (i : Fin n), ∀ ℓ ∈ D.leavesOf i,
        pd (pd (D.gfun c φ) ℓ) ℓ y = D.adjB c φ y (.leaf ℓ)) ∧
      ∀ (i i' : Fin n), ∀ ℓ ∈ D.leavesOf i, ∀ ℓ' ∈ D.leavesOf i', ∀ w < D.size, D.IsOp w →
        D.Below (.leaf ℓ) (D.child w 0) → D.Below (.leaf ℓ') (D.child w 1) →
          pd (pd (D.gfun c φ) ℓ) ℓ' y =
            D.Kfac c φ y w * D.dpath c φ y (D.child w 0) (.leaf ℓ) *
              D.dpath c φ y (D.child w 1) (.leaf ℓ') := by sorry

end CancelFreeHessian.Formula
