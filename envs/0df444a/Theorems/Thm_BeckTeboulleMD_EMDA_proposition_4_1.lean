-- Prove2me | Theorems.Thm_BeckTeboulleMD_EMDA_proposition_4_1
-- name    : BeckTeboulleMD.EMDA.proposition_4_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T05:53:53.669046+00:00
-- url     : https://prove2.me/theorems/6ebbe7d6-8a5a-49b6-906c-215b5c5a992f
-- title:
--   Proposition 4.1, p. 172 — inf_{z>0} (c + (2σ)⁻¹zᵀDz)/(bᵀz) = √(2c/(σ bᵀD⁻¹b)), attained at z* = √(2cσ/bᵀD⁻¹b) D⁻¹b
-- statement:
--   Let $d \ge 1$, $c > 0$, $\sigma > 0$, $b \in \mathbb R^d_{++}$ (all entries positive), and let $D$ be a symmetric positive definite $d \times d$ matrix such that $D^{-1}b \in \mathbb R^d_{++}$. Write $q = b^{\mathsf T} D^{-1} b$. Then
--   $$\inf_{z \in \mathbb R^d_{++}} \frac{c + (2\sigma)^{-1} z^{\mathsf T} D z}{b^{\mathsf T} z} = \sqrt{\frac{2c}{\sigma q}},$$
--   with optimal solution $z^* = \sqrt{2c\sigma / q}\; D^{-1} b \in \mathbb R^d_{++}$.
--
--   The proposition gives the optimal step sizes in the efficiency estimate (4.22): with $D = L_f^2 I$ and $b = e$ it produces the constant step of Theorem 4.2.
--
--   **Formalization Note** The statement is given as three facts: every $z > 0$ has value at least $\sqrt{2c/(\sigma q)}$; $z^*$ has positive entries; and $z^*$ attains that value. The hypothesis $D^{-1}b \in \mathbb R^d_{++}$ is an addition to the page, which is needed: without it the proposition is false. For $d = 2$, $b = (1,1)$, $D = \begin{pmatrix}1 & 0.5\\ 0.5 & 0.3\end{pmatrix}$, $c = \sigma = 1$, one has $D^{-1}b = (-4, 10)$, the infimum over $\mathbb R^2_{++}$ is about $0.775$, while $\sqrt{2c/(\sigma q)} \approx 0.577$, and $z^*$ has a negative entry. The only use of the proposition in the paper ($D = L_f^2 I$, $b = e$) satisfies it. $\sigma$ is the strong convexity parameter of $\psi$, positive by assumption; $d \ge 1$ excludes the empty orthant.
-- source:
--   Beck & Teboulle, Mirror descent and nonlinear projected subgradient methods for convex optimization, Oper. Res. Lett. 31 (2003), p. 172, Proposition 4.1

import Mathlib
import Definitions.Def_BeckTeboulleMD_EMDA_Setting

open Matrix

namespace BeckTeboulleMD.EMDA

/-- Proposition 4.1, p. 172, with the disclosed addition `D⁻¹b > 0`: for `c > 0`, `σ > 0`,
`b ∈ ℝ^d_{++}` and `D` symmetric positive definite with `D⁻¹b ∈ ℝ^d_{++}`, writing `q = bᵀD⁻¹b`,
`inf_{z ∈ ℝ^d_{++}} (c + (2σ)⁻¹ zᵀDz) / (bᵀz) = √(2c / (σ q))`, attained at
`z* = √(2cσ / q) D⁻¹b`. -/
theorem proposition_4_1 {d : ℕ} (hd : 0 < d) (c σ : ℝ) (hc : 0 < c) (hσ : 0 < σ)
    (b : Fin d → ℝ) (hb : ∀ i, 0 < b i)
    (D : Matrix (Fin d) (Fin d) ℝ) (hD : D.PosDef)
    (hDb : ∀ i, 0 < (D⁻¹ *ᵥ b) i) :
    (∀ z : Fin d → ℝ, (∀ i, 0 < z i) →
        Real.sqrt (2 * c / (σ * (b ⬝ᵥ (D⁻¹ *ᵥ b))))
          ≤ (c + 1 / (2 * σ) * (z ⬝ᵥ (D *ᵥ z))) / (b ⬝ᵥ z)) ∧
    (∀ i, 0 < (Real.sqrt (2 * c * σ / (b ⬝ᵥ (D⁻¹ *ᵥ b))) • (D⁻¹ *ᵥ b)) i) ∧
    (c + 1 / (2 * σ) * ((Real.sqrt (2 * c * σ / (b ⬝ᵥ (D⁻¹ *ᵥ b))) • (D⁻¹ *ᵥ b))
          ⬝ᵥ (D *ᵥ (Real.sqrt (2 * c * σ / (b ⬝ᵥ (D⁻¹ *ᵥ b))) • (D⁻¹ *ᵥ b)))))
        / (b ⬝ᵥ (Real.sqrt (2 * c * σ / (b ⬝ᵥ (D⁻¹ *ᵥ b))) • (D⁻¹ *ᵥ b)))
      = Real.sqrt (2 * c / (σ * (b ⬝ᵥ (D⁻¹ *ᵥ b)))) := by sorry

end BeckTeboulleMD.EMDA
