-- Prove2me | Theorems.Thm_BoydADMM_ModelFit_group_lasso_block_update
-- name    : BoydADMM.ModelFit.group_lasso_block_update
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T08:37:35.9427+00:00
-- url     : https://prove2.me/theorems/cf03b34b-0280-48ac-b72f-6d830747b2e6
-- title:
--   §8.3.2, pp. 69–70 — the group-lasso block update is 0 iff ‖Aᵢᵀv‖₂ ≤ λ/ρ, else (AᵢᵀAᵢ + νI)⁻¹Aᵢᵀv with ν‖xᵢ‖₂ = λ/ρ
-- statement:
--   In the feature-split group lasso, each $x_i$-update minimizes a function of the form
--   $$h(x)=\frac{\rho}{2}\|A_ix-v\|_2^2+\lambda\|x\|_2,\qquad x\in\mathbb R^{n_i},$$
--   where $A_i\in\mathbb R^{m\times n_i}$, $v\in\mathbb R^m$, $\rho>0$ and $\lambda>0$ (note the $\ell_2$ norm is not squared). For $\nu>0$ write $x(\nu)=(A_i^TA_i+\nu I)^{-1}A_i^Tv$. Then:
--
--   1. $0$ minimizes $h$ if and only if $\|A_i^Tv\|_2\le\lambda/\rho$; and in that case $0$ is the only minimizer.
--   2. If $\|A_i^Tv\|_2>\lambda/\rho$, then
--      - there is exactly one $\nu>0$ with $\nu\,\|x(\nu)\|_2=\lambda/\rho$;
--      - for every $\nu>0$ with $\nu\,\|x(\nu)\|_2=\lambda/\rho$, the point $x(\nu)$ minimizes $h$;
--      - every minimizer $x$ of $h$ has the form $x=x(\nu)$ for some $\nu>0$ with $\nu\|x\|_2=\lambda/\rho$.
--
--   So in both cases $h$ has a unique minimizer, which is $0$ exactly when $\|A_i^Tv\|_2\le\lambda/\rho$ and otherwise a ridge-regression solution whose parameter $\nu$ is pinned down by $\nu\|x_i\|_2=\lambda/\rho$ and can be found by a one-parameter search.
--
--   This is the closed form behind the $x_i$-update of distributed group lasso: each block either drops out entirely or solves a ridge problem with a data-dependent ridge parameter.
--
--   **Formalization Note** The book writes "the solution", "the value of $\nu$". The statement asserts existence and uniqueness of that $\nu$ and characterizes every minimizer, rather than assuming either; uniqueness of the minimizer in case 1 and case 2 is then a consequence, not a hypothesis (no invertibility of $A_i^TA_i$ is assumed). $(A_i^TA_i+\nu I)^{-1}$ is Mathlib's matrix inverse, which is the true inverse for $\nu>0$. $\lambda$ is `lam` in Lean.
-- source:
--   Boyd, Parikh, Chu, Peleato, Eckstein, Distributed Optimization and Statistical Learning via the Alternating Direction Method of Multipliers, Found. Trends Mach. Learn. 3(1) (2011), pp. 69–70, §8.3.2

import Mathlib
import Definitions.Def_BoydADMM_ModelFit_Basic

open Matrix

namespace BoydADMM.ModelFit

/-- §8.3.2, pp. 69–70 (goal): the minimizer of `h(x) = (ρ/2)‖Aᵢx − v‖₂² + λ‖x‖₂` is `0` iff
`‖Aᵢᵀv‖₂ ≤ λ/ρ`; otherwise it is `(AᵢᵀAᵢ + νI)⁻¹Aᵢᵀv` for the value `ν > 0` with
`ν‖xᵢ‖₂ = λ/ρ`. -/
theorem group_lasso_block_update {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (v : EuclideanSpace ℝ (Fin m)) (ρ lam : ℝ) (hρ : 0 < ρ) (hlam : 0 < lam) :
    (IsMinOn (groupLassoObj ρ lam A v) Set.univ 0 ↔
        ‖Matrix.toEuclideanLin Aᵀ v‖ ≤ lam / ρ) ∧
    (‖Matrix.toEuclideanLin Aᵀ v‖ ≤ lam / ρ →
        ∀ x, IsMinOn (groupLassoObj ρ lam A v) Set.univ x → x = 0) ∧
    (lam / ρ < ‖Matrix.toEuclideanLin Aᵀ v‖ →
        (∃! ν : ℝ, 0 < ν ∧ ν * ‖ridgeSol A ν v‖ = lam / ρ) ∧
        (∀ ν : ℝ, 0 < ν → ν * ‖ridgeSol A ν v‖ = lam / ρ →
          IsMinOn (groupLassoObj ρ lam A v) Set.univ (ridgeSol A ν v)) ∧
        (∀ x, IsMinOn (groupLassoObj ρ lam A v) Set.univ x →
          ∃ ν : ℝ, 0 < ν ∧ ν * ‖x‖ = lam / ρ ∧ x = ridgeSol A ν v)) := by sorry

end BoydADMM.ModelFit
