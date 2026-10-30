-- Prove2me | Theorems.Thm_BeckTeboulleMD_EMDA_step_size_optimization
-- name    : BeckTeboulleMD.EMDA.step_size_optimization
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:00:28.935991+00:00
-- url     : https://prove2.me/theorems/b5de331b-d064-4bcd-881d-70c198c008ee
-- title:
--   Proposition 4.1 — optimal step sizes (corrected: requires $D^{-1}b>0$)
-- statement:
--   Let $c>0$, $\sigma>0$, $b\in\mathbb R^d_{++}$ (all entries positive) and $D$ a symmetric positive definite $d\times d$ real matrix such that every entry of $D^{-1}b$ is positive. Then
--   $$
--   \min_{z\in\mathbb R^d_{++}}\frac{c+(2\sigma)^{-1}z^{\mathsf T}Dz}{b^{\mathsf T}z}=\sqrt{\frac{2c}{\sigma\,b^{\mathsf T}D^{-1}b}},
--   $$
--   that is, this value is a lower bound for the ratio at every $z\in\mathbb R^d_{++}$ and is attained; moreover the point
--   $$
--   z^*=\sqrt{\frac{2c\sigma}{b^{\mathsf T}D^{-1}b}}\;D^{-1}b
--   $$
--   lies in $\mathbb R^d_{++}$ and attains it.
--
--   In the paper this proposition chooses the step sizes $t_1,\dots,t_k$ minimizing the right-hand side of the efficiency bound (4.22), with $c=B_\psi(x^*,x^1)$, $b=e$ and $D=L_f^2I$; it yields the step rule (4.23) of Theorem 4.2.
--
--   **Formalization Note** The infimum with its minimizer is stated as "least element of the set of values of the ratio over $z\in\mathbb R^d_{++}$" together with positivity of $z^*$ and the value at $z^*$.
--
--   Differences from the source:
--   - correction: no condition on D⁻¹b → adds ∀ i, 0 < (D⁻¹ b)_i; reason: the printed statement is false: d = 2, σ = c = 1, b = (1, 1/10), D = [[1, 9/10], [9/10, 1]] (symmetric, eigenvalues 1.9 and 0.1) gives D⁻¹b = (0.91, −0.8)/0.19 ∉ ℝ²₊₊, claimed value √(2/bᵀD⁻¹b) ≈ 0.677, but every z > 0 has ratio ≥ 2/√2.02 ≈ 1.407; the added condition is exactly z* ∈ ℝ^d_{++} and holds in the paper's only use D = L_f² I, b = e
--   - reading: σ appears without being introduced in the proposition → 0 < σ is a hypothesis; reason: σ is the paper's standing strong convexity parameter σ > 0 (§2)
--   - encoding: d ≥ 1 implicit (ℝ^d_{++} with a positive definite d × d matrix) → d : ℕ arbitrary, d = 0 allowed; reason: at d = 0 the paper's ratio divides by bᵀz = 0 and is undefined; Lean's a/0 = 0 makes both sides 0, so no paper instance is changed
-- source:
--   Beck & Teboulle, Mirror descent and nonlinear projected subgradient methods for convex optimization, Oper. Res. Lett. 31 (2003) 167–175, doi:10.1016/s0167-6377(02)00231-6, §4, Proposition 4.1, printed p. 172 (PDF p. 6)

import Mathlib

open Matrix

namespace BeckTeboulleMD.EMDA

/-- **Proposition 4.1 — optimal step sizes (corrected: requires `D⁻¹b > 0`).**
Beck & Teboulle, *Mirror descent and nonlinear projected subgradient methods for convex
optimization*, Oper. Res. Lett. 31 (2003), §4, Proposition 4.1,
printed p. 172 (PDF p. 6): "Given c > 0, b ∈ ℝ^d_{++} and D a symmetric positive definite matrix
one has inf_{z∈ℝ^d_{++}} [c + (2σ)⁻¹ zᵀDz] / (bᵀz) = √(2c / (σ bᵀD⁻¹b)) with optimal solution
z* = √(2cσ / bᵀD⁻¹b) D⁻¹b."

The conclusion has two parts: the value `√(2c/(σ bᵀD⁻¹b))` is the least element of the set of
values of the ratio over `z ∈ ℝ^d_{++}` (so the infimum is a minimum), and `z*` lies in
`ℝ^d_{++}` and attains it.

**Formalization Note.** The hypothesis `∀ i, 0 < (D⁻¹ *ᵥ b) i` is a correction: without it the
printed statement is false (`d = 2`, `σ = c = 1`, `b = (1, 1/10)`, `D = [[1, 9/10], [9/10, 1]]`:
the claimed value is `≈ 0.677` but every `z > 0` gives a ratio `≥ 2/√2.02 ≈ 1.407`). It holds in
the paper's only use, `D = L_f² I`, `b = e`. `σ > 0` is the paper's standing strong convexity
parameter. `Matrix.PosDef` over `ℝ` includes symmetry. For `d = 0` both sides are `0` by Lean's
`a / 0 = 0` and the statement holds trivially. -/
theorem step_size_optimization {d : ℕ} (c σ : ℝ) (hc : 0 < c) (hσ : 0 < σ)
    (b : Fin d → ℝ) (hb : ∀ i, 0 < b i) (D : Matrix (Fin d) (Fin d) ℝ) (hD : D.PosDef)
    (hDb : ∀ i, 0 < (D⁻¹ *ᵥ b) i) :
    IsLeast {v : ℝ | ∃ z : Fin d → ℝ, (∀ i, 0 < z i) ∧
        v = (c + (2 * σ)⁻¹ * (z ⬝ᵥ (D *ᵥ z))) / (b ⬝ᵥ z)}
      (Real.sqrt (2 * c / (σ * (b ⬝ᵥ (D⁻¹ *ᵥ b))))) ∧
    (∀ i, 0 < (Real.sqrt (2 * c * σ / (b ⬝ᵥ (D⁻¹ *ᵥ b))) • (D⁻¹ *ᵥ b)) i) ∧
    (c + (2 * σ)⁻¹ * ((Real.sqrt (2 * c * σ / (b ⬝ᵥ (D⁻¹ *ᵥ b))) • (D⁻¹ *ᵥ b)) ⬝ᵥ
        (D *ᵥ (Real.sqrt (2 * c * σ / (b ⬝ᵥ (D⁻¹ *ᵥ b))) • (D⁻¹ *ᵥ b))))) /
        (b ⬝ᵥ (Real.sqrt (2 * c * σ / (b ⬝ᵥ (D⁻¹ *ᵥ b))) • (D⁻¹ *ᵥ b))) =
      Real.sqrt (2 * c / (σ * (b ⬝ᵥ (D⁻¹ *ᵥ b)))) := by sorry

end BeckTeboulleMD.EMDA
