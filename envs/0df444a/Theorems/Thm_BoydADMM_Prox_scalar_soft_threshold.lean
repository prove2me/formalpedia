-- Prove2me | Theorems.Thm_BoydADMM_Prox_scalar_soft_threshold
-- name    : BoydADMM.Prox.scalar_soft_threshold
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T01:54:58.353232+00:00
-- url     : https://prove2.me/theorems/beb47c8f-8da5-43e0-b488-ddc575050aa8
-- title:
--   §4.4.3, p. 32 — the scalar x_i-update for λ|x_i| is x_i⁺ = S_{λ/ρ}(v_i)
-- statement:
--   Let $\lambda>0$, $\rho>0$ and $v_i\in\mathbb R$. The scalar problem
--   $$x_i^+=\operatorname*{argmin}_{x_i}\Bigl(\lambda|x_i|+\tfrac{\rho}{2}(x_i-v_i)^2\Bigr)$$
--   has the unique solution
--   $$x_i^+=S_{\lambda/\rho}(v_i).$$
--   That is, $t\in\mathbb R$ minimizes $\lambda|t|+\tfrac{\rho}{2}(t-v_i)^2$ over $\mathbb R$ if and only if $t=S_{\lambda/\rho}(v_i)$.
--
--   This is the scalar update that component separability (§4.4.2) reduces the $\ell_1$-regularized $x$-update to.
--
--   **Formalization Note** The book writes "the solution"; the objective is strictly convex, so we state that $S_{\lambda/\rho}(v_i)$ is a minimizer and the only one, as an equivalence. $\lambda$ is written `lam` because `λ` is a Lean keyword.
-- source:
--   Boyd, Parikh, Chu, Peleato, Eckstein, Distributed Optimization and Statistical Learning via the Alternating Direction Method of Multipliers, Found. Trends Mach. Learn. 3(1) (2011), p. 32, §4.4.3

import Mathlib
import Definitions.Def_BoydADMM_Prox_Basic

open Matrix

namespace BoydADMM.Prox

theorem scalar_soft_threshold (lam ρ : ℝ) (hlam : 0 < lam) (hρ : 0 < ρ) (a t : ℝ) :
    (∀ s : ℝ, lam * |t| + (ρ / 2) * (t - a) ^ 2 ≤ lam * |s| + (ρ / 2) * (s - a) ^ 2) ↔
      t = softThreshold (lam / ρ) a := by sorry

end BoydADMM.Prox
