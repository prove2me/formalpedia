-- Prove2me | Theorems.Thm_BoydADMM_L1_group_lasso_z_update
-- name    : BoydADMM.L1.group_lasso_z_update
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T08:05:47.629027+00:00
-- url     : https://prove2.me/theorems/ced4f7ab-c52f-44e1-9038-60e82911008b
-- title:
--   §6.4.2, p. 45 — the group-lasso z-update is block soft thresholding $z_i^{k+1}=\mathcal S_{\lambda/\rho}(x_i^{k+1}+u_i^k)$
-- statement:
--   Let $x=(x_1,\dots,x_N)$ and $u=(u_1,\dots,u_N)$ be partitioned into blocks $x_i,u_i\in\mathbb R^{n_i}$, and let $\lambda\ge0$, $\rho>0$. The block vector $z^\star$ with blocks
--   $$z^\star_i=\mathcal S_{\lambda/\rho}(x_i+u_i),\qquad i=1,\dots,N,$$
--   where $\mathcal S_\kappa(a)=(1-\kappa/\|a\|_2)_+a$ (with $\mathcal S_\kappa(0)=0$) is vector soft thresholding, is the unique minimizer over all block vectors $z=(z_1,\dots,z_N)$ of
--   $$\lambda\sum_{i=1}^N\|z_i\|_2+\frac\rho2\sum_{i=1}^N\|x_i-z_i+u_i\|_2^2 .$$
--
--   With $x=x^{k+1}$ and $u=u^k$ this is the z-update of ADMM for the group lasso, whose regularizer $\sum_i\|x_i\|_2$ is separable across blocks but not within them.
--
--   **Formalization Note** The book prints $u^k$ in the block update; since $u$ is partitioned like $x$, the intended term is the block $u_i^k$, which is what is stated. The block sizes $n_i$ are arbitrary (`nb : Fin N → ℕ`), and blocks are indexed from $0$. $\lambda$ is called `lam`; the book takes $\lambda>0$, the statement allows $\lambda\ge0$.
-- source:
--   Boyd, Parikh, Chu, Peleato, Eckstein, Distributed Optimization and Statistical Learning via the Alternating Direction Method of Multipliers, Found. Trends Mach. Learn. 3(1) (2011), p. 45, §6.4.2 (group lasso, block soft thresholding)

import Mathlib
import Definitions.Def_BoydADMM_L1_Basic

open Matrix

namespace BoydADMM.L1

/-- §6.4.2, p. 45: let `x = (x_1, …, x_N)` and `u = (u_1, …, u_N)` be partitioned into blocks
`x_i, u_i ∈ ℝ^{n_i}`. For `λ ≥ 0` (called `lam`) and `ρ > 0`, the block vector with blocks
`S_{λ/ρ}(x_i + u_i)` (vector soft thresholding) is the unique minimizer of
`λ ∑_i ‖z_i‖₂ + (ρ/2) ∑_i ‖x_i − z_i + u_i‖₂²` over all block vectors `z`. -/
theorem group_lasso_z_update {N : ℕ} (nb : Fin N → ℕ) (lam ρ : ℝ) (hlam : 0 ≤ lam) (hρ : 0 < ρ)
    (x u : (i : Fin N) → EuclideanSpace ℝ (Fin (nb i))) :
    IsUniqueMinimizerOn
      (fun z : (i : Fin N) → EuclideanSpace ℝ (Fin (nb i)) =>
        lam * ∑ i, ‖z i‖ + (ρ / 2) * ∑ i, ‖x i - z i + u i‖ ^ 2) Set.univ
      (fun i => blockSoftThreshold (lam / ρ) (x i + u i)) := by sorry

end BoydADMM.L1
