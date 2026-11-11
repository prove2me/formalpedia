-- Prove2me | Theorems.Thm_DiscIsoCurvature_Cube_theorem_6_8
-- name    : DiscIsoCurvature.Cube.theorem_6_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:08:21.193336+00:00
-- url     : https://prove2.me/theorems/aa64c781-8bb9-432e-ab5c-6f57afe503fa
-- title:
--   Theorem 6.8 (Marton) — (1/n)Ent_µ[f²] ≤ 2/(α(1 − ‖R‖₂)²)⟨f, (I − G)f⟩_µ for the Gibbs sampler on Xⁿ
-- statement:
--   Let $\mathcal X$ be a finite set and $\mu$ a distribution on $\Omega=\mathcal X^n$ with $\|R\|_2<1$ ($R$ the Dobrushin matrix of Definition 6.6) and $\alpha=\min_{i,x}\mu_i(x_i\mid x_{-i})>0$. For the Gibbs sampler $G=\frac1n\sum_iK_i$, $K_i(z\mid y)=\mathbf 1[z_{-i}=y_{-i}]\mu_i(z_i\mid z_{-i})$, and every $f:\Omega\to\mathbb R$,
--   $$\frac1n\,\mathrm{Ent}_\mu[f^2]\le\frac{2}{\alpha(1-\|R\|_2)^2}\,\langle f,(I-G)f\rangle_\mu .$$
--   This is Marton's log-Sobolev inequality for Glauber dynamics under the $L^2$ Dobrushin condition, cited from [Mar19, Theorem 1.14 and Corollary 1.11].
--
--   Differences from the source:
--
--   - encoding: Ω = Xⁿ, [n] → Fin n → X with [Fintype X] [DecidableEq X]; reason: the product of n copies of the finite alphabet
--   - encoding: ⟨f, (I − G)f⟩_µ → E_µ[f (f − G f)] with (G f)(y) = ∑_z G(z | y) f(z); reason: the µ-inner product of f and (I − G)f
-- source:
--   Chen, Chen, Zhang, Discrete Isoperimetric Inequalities via Curvature, arXiv:2609.24687 (version of November 3, 2026, sha256 ec30d304…), p. 38, Theorem 6.8

import Mathlib
import Definitions.Def_DiscIsoCurvature_Cube_Basic
import Definitions.Def_DiscIsoCurvature_Cube_Dobrushin

namespace DiscIsoCurvature.Cube

/-- Theorem 6.8 (Marton; p. 38): for a finite alphabet `X` and a distribution `μ` on
`Ω = X^n` with `‖R‖₂ < 1` (`R` of Definition 6.6) and `α = min_{i, x} μᵢ(xᵢ | x₋ᵢ) > 0`,
for every `f : Ω → ℝ`, `(1/n) Ent_μ[f²] ≤ 2/(α(1 − ‖R‖₂)²) ⟨f, (I − G) f⟩_μ`, `G` the Gibbs
sampler. -/
theorem theorem_6_8 {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ} (μ : (Fin n → X) → ℝ)
    (hμ : IsDist μ) (hR : specNorm (dobrushinMatrix μ) < 1) (hα : 0 < minCondMarginal μ)
    (f : (Fin n → X) → ℝ) :
    (1 / (n : ℝ)) * ent μ (fun x => f x ^ 2) ≤
      2 / (minCondMarginal μ * (1 - specNorm (dobrushinMatrix μ)) ^ 2) * gibbsDirichlet μ f := by sorry

end DiscIsoCurvature.Cube
