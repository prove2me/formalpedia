-- Prove2me | Theorems.Thm_BeckTeboulleMD_EMDA_proposition_5_1_a
-- name    : BeckTeboulleMD.EMDA.proposition_5_1_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T05:54:17.416951+00:00
-- url     : https://prove2.me/theorems/3156ca2f-e11d-4207-8bdd-aba675483b56
-- title:
--   Proposition 5.1(a), p. 173 — ψ_e is 1-strongly convex on int Δ w.r.t. ‖·‖₁: Σ(x_j − y_j) ln(x_j/y_j) ≥ ‖x − y‖₁²
-- statement:
--   Let $\psi_e(x) = \sum_{j=1}^n x_j \ln x_j$ be the entropy and $\operatorname{int}\Delta = \{x \in \mathbb R^n : x_j > 0,\ \sum_j x_j = 1\}$. Then for all $x, y \in \operatorname{int}\Delta$:
--
--   1. $\langle \nabla\psi_e(x) - \nabla\psi_e(y),\ x - y\rangle = \sum_{j=1}^n (x_j - y_j)\ln\dfrac{x_j}{y_j}$;
--   2. $$\sum_{j=1}^n (x_j - y_j)\ln\frac{x_j}{y_j} \ge \|x - y\|_1^2;$$
--   3. $\psi_e$ is $1$-strongly convex over $\operatorname{int}\Delta$ with respect to $\|\cdot\|_1$: for $a, b \ge 0$ with $a + b = 1$,
--   $$\psi_e(a x + b y) \le a\psi_e(x) + b\psi_e(y) - \tfrac12\, a b\, \|x - y\|_1^2.$$
--
--   The strong convexity constant $\sigma = 1$ with respect to the $\ell_1$ norm is what makes the entropic mirror descent bound depend on the dimension only through $\ln n$.
--
--   **Formalization Note** $\|x - y\|_1$ is written $\sum_j |x_j - y_j|$, and the strong convexity is written out explicitly instead of through a normed space carrying the $\ell_1$ norm; it is Mathlib's notion of strong convexity with parameter $1$ for that norm. $\nabla\psi_e(x)$ is the Fréchet derivative of $\psi_e$ on $\mathbb R^n$ (which does not depend on the norm). "$\operatorname{int}\Delta$" is the relative interior of $\Delta$, since $\Delta$ has empty interior in $\mathbb R^n$.
-- source:
--   Beck & Teboulle, Mirror descent and nonlinear projected subgradient methods for convex optimization, Oper. Res. Lett. 31 (2003), p. 173, Proposition 5.1(a)

import Mathlib
import Definitions.Def_BeckTeboulleMD_EMDA_Setting

namespace BeckTeboulleMD.EMDA

/-- Proposition 5.1(a), p. 173: on the relative interior of the unit simplex,
`⟨∇ψ_e(x) − ∇ψ_e(y), x − y⟩ = ∑_j (x_j − y_j) ln(x_j / y_j) ≥ ‖x − y‖₁²`,
and `ψ_e` is `1`-strongly convex there with respect to `‖·‖₁`. -/
theorem proposition_5_1_a {n : ℕ} :
    (∀ x ∈ relIntSimplex n, ∀ y ∈ relIntSimplex n,
      (fderiv ℝ (entropy (n := n)) x - fderiv ℝ (entropy (n := n)) y) (x - y)
        = ∑ j, (x j - y j) * Real.log (x j / y j)) ∧
    (∀ x ∈ relIntSimplex n, ∀ y ∈ relIntSimplex n,
      (∑ j, |x j - y j|) ^ 2 ≤ ∑ j, (x j - y j) * Real.log (x j / y j)) ∧
    (∀ x ∈ relIntSimplex n, ∀ y ∈ relIntSimplex n, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      entropy (a • x + b • y)
        ≤ a * entropy x + b * entropy y - a * b * (1 / 2 * (∑ j, |x j - y j|) ^ 2)) := by sorry

end BeckTeboulleMD.EMDA
