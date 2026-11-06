-- Prove2me | Theorems.Thm_ConstrSOSP_hermite_corner_data
-- name    : ConstrSOSP.hermite_corner_data
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:58:43.992756+00:00
-- url     : https://prove2.me/theorems/5e0b5d50-c01e-4099-b335-d88128e0827c
-- title:
--   The Hermite polynomial (17) meets all 36 interpolation conditions
-- statement:
--   Let $f_\sigma$ be the biquintic polynomial (17) on the unit cell, built from corner values $z_{ij}$, corner gradients $(\xi_{ij},\eta_{ij})$ and the diagonal second derivative $\sigma$.
--
--   **Theorem.** $f_\sigma$ has degree at most five in each variable, and at each corner $(i,j)\in\{0,1\}^2$
--   $$
--   f_\sigma=z_{ij},\quad \partial_xf_\sigma=\xi_{ij},\quad \partial_yf_\sigma=\eta_{ij},\quad \partial_{xx}f_\sigma=\partial_{yy}f_\sigma=\sigma,
--   $$
--   $$
--   \partial_{xy}f_\sigma=\partial_{xyy}f_\sigma=\partial_{xxy}f_\sigma=\partial_{xxyy}f_\sigma=0 .
--   $$
--
--   These are the nine conditions per corner encoded by $AC^{a,b}A^\top=V^{a,b}$ in §5.2, so (17) is the interpolant used throughout the construction.
--
--   Differences from the source:
--   - encoding: partial derivatives of f_σ at the corners → iterated one-variable derivatives (deriv) of the polynomial; reason: Lean convention; same values for a polynomial
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), (17), pp.33–34

import Mathlib
import Definitions.Def_ConstrSOSP_fsigma

namespace ConstrSOSP

/-- **The Hermite polynomial (17) meets the 36 interpolation conditions** (arXiv:2604.02285,
2 Nov 2026, pp.33–34: "Thus the last term imposes f_xx = f_yy = σ at every corner without changing
its value or gradient. At every corner, the mixed derivatives satisfy ∂²f_σ/∂x∂y = ∂³f_σ/∂x∂y² =
∂³f_σ/∂x²∂y = ∂⁴f_σ/∂x²∂y² = 0. … The polynomial in (17) has degree at most five in each variable
and satisfies all 36 interpolation conditions.").

For every `σ` and corner data `z, ξ, η`, the polynomial `f_σ` of (17) has degree at most five in
each variable, and at each corner `(i, j) ∈ {0, 1}²` it has value `z_{ij}`, gradient
`(ξ_{ij}, η_{ij})`, `f_xx = f_yy = σ`, and `f_xy = f_xyy = f_xxy = f_xxyy = 0`. -/
theorem hermite_corner_data (σ : ℝ) (z ξ η : Fin 2 → Fin 2 → ℝ) :
    (∃ c : Fin 6 → Fin 6 → ℝ, ∀ x y : ℝ,
      fsigma σ z ξ η x y = ∑ i : Fin 6, ∑ j : Fin 6, c i j * x ^ (i : ℕ) * y ^ (j : ℕ)) ∧
    ∀ i j : Fin 2,
      fsigma σ z ξ η (i : ℕ) (j : ℕ) = z i j ∧
      deriv (fun x => fsigma σ z ξ η x (j : ℕ)) (i : ℕ) = ξ i j ∧
      deriv (fun y => fsigma σ z ξ η (i : ℕ) y) (j : ℕ) = η i j ∧
      deriv (deriv (fun x => fsigma σ z ξ η x (j : ℕ))) (i : ℕ) = σ ∧
      deriv (deriv (fun y => fsigma σ z ξ η (i : ℕ) y)) (j : ℕ) = σ ∧
      deriv (fun y => deriv (fun x => fsigma σ z ξ η x y) (i : ℕ)) (j : ℕ) = 0 ∧
      deriv (deriv (fun y => deriv (fun x => fsigma σ z ξ η x y) (i : ℕ))) (j : ℕ) = 0 ∧
      deriv (fun y => deriv (deriv (fun x => fsigma σ z ξ η x y)) (i : ℕ)) (j : ℕ) = 0 ∧
      deriv (deriv (fun y => deriv (deriv (fun x => fsigma σ z ξ η x y)) (i : ℕ))) (j : ℕ) = 0 := by sorry

end ConstrSOSP
