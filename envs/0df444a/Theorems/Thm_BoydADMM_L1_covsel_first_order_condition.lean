-- Prove2me | Theorems.Thm_BoydADMM_L1_covsel_first_order_condition
-- name    : BoydADMM.L1.covsel_first_order_condition
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T08:21:21.434644+00:00
-- url     : https://prove2.me/theorems/70cfe195-2654-475e-b6eb-851fe225bcff
-- title:
--   §6.5, p. 47 — first-order condition: $X\succ0$ is the X-update iff $S-X^{-1}+\rho(X-Z^k+U^k)=0$
-- statement:
--   Let $S,Z,U\in\mathbb R^{n\times n}$ with $S$ and $Z-U$ symmetric, and let $\rho>0$. Consider
--   $$F(X)=\operatorname{Tr}(SX)-\log\det X+\frac\rho2\|X-Z+U\|_F^2$$
--   on the cone $\mathbb S^n_{++}$ of symmetric positive definite matrices. For $X\in\mathbb S^n_{++}$,
--   $$F(X)\le F(X')\ \text{ for all } X'\in\mathbb S^n_{++}\quad\Longleftrightarrow\quad S-X^{-1}+\rho(X-Z+U)=0 .$$
--
--   This is the book's statement that "the first-order optimality condition is that the gradient should vanish, together with the implicit constraint $X\succ0$": the vanishing gradient is necessary and, because $F$ is convex, sufficient for $X$ to solve the X-minimization.
--
--   **Formalization Note** $Z,U$ stand for $Z^k,U^k$. The symmetry of $S$ (an empirical covariance) and of $Z-U$ (the ADMM iterates are symmetric when started symmetric) is made an explicit hypothesis; without it the gradient over symmetric matrices is only the symmetric part of $S-X^{-1}+\rho(X-Z+U)$. $\mathbb S^n_{++}$ is `Matrix.PosDef`, which includes symmetry. $\|\cdot\|_F^2$ is the sum of squared entries.
-- source:
--   Boyd, Parikh, Chu, Peleato, Eckstein, Distributed Optimization and Statistical Learning via the Alternating Direction Method of Multipliers, Found. Trends Mach. Learn. 3(1) (2011), p. 47, §6.5 (first-order optimality condition)

import Mathlib
import Definitions.Def_BoydADMM_L1_CovSel

open Matrix

namespace BoydADMM.L1

/-- §6.5, p. 47: for symmetric `S` and `Z − U` and `ρ > 0`, a positive definite `X` minimizes
`Tr(SX) − log det X + (ρ/2)‖X − Z + U‖_F²` over the positive definite matrices if and only if
the gradient vanishes, `S − X⁻¹ + ρ(X − Z + U) = 0`. -/
theorem covsel_first_order_condition {n : ℕ} (S Z U : Matrix (Fin n) (Fin n) ℝ) (ρ : ℝ)
    (hρ : 0 < ρ) (hS : S.IsSymm) (hZU : (Z - U).IsSymm)
    (X : Matrix (Fin n) (Fin n) ℝ) (hX : X.PosDef) :
    (∀ X' : Matrix (Fin n) (Fin n) ℝ, X'.PosDef →
        covselXObjective S Z U ρ X ≤ covselXObjective S Z U ρ X') ↔
      S - X⁻¹ + ρ • (X - Z + U) = 0 := by sorry

end BoydADMM.L1
