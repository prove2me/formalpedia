-- Prove2me | Theorems.Thm_Complex_norm_one_sub_inv_exp_and_sq_mul_log_eq_and_contDiff
-- name    : Complex.norm_one_sub_inv_exp_and_sq_mul_log_eq_and_contDiff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/6680e786-fcee-576b-99fc-abe2b3dd45e7
-- title:
--   Inversion identities for ‖1-exp(X/2+2π iTheta)⁻¹‖
-- statement:
--   The statement is a conjunction of four assertions about the complex number $\zeta = \exp(X/2 + 2\pi i\Theta)$, written in Lean as `Complex.exp ((X/2 : ℝ) + 2 * Real.pi * Complex.I * Θ)`, with no hypotheses. First, for all real $X$ and $\Theta$, $\|1-\zeta^{-1}\| = e^{-X/2}\,\|1-\zeta\|$. Second, for all real $X$ and $\Theta$, $$\|1-\zeta^{-1}\|^2\log\|1-\zeta^{-1}\| = e^{-X}\Bigl(\|1-\zeta\|^2\log\|1-\zeta\| - \tfrac{X}{2}\,\|1-\zeta\|^2\Bigr),$$ where $\log$ is the real logarithm with the usual convention $\log 0 = 0$, so that the identity holds also in the degenerate case $\zeta = 1$. Third, for all real $X$ and $\Theta$, the squared distance is the trigonometric expression $\|1-\zeta\|^2 = 1 - 2e^{X/2}\cos(2\pi\Theta) + e^{X}$. Fourth, the function $\mathbb{R}^2 \to \mathbb{R}$ given by $(x,\theta) \mapsto 1 - 2e^{x/2}\cos(2\pi\theta) + e^{x}$ is $C^\infty$ on $\mathbb{R}^2$ in the sense of `ContDiff ℝ ⊤`.
--
--   An elementary computation packaging the behaviour, under $u \mapsto u^{-1}$, of the archimedean weight $\|1-u\|^2\log\|1-u\|$ at a complex place written in polar coordinates $u = \exp(x/2 + 2\pi i\theta)$, together with the smoothness of the squared distance in those coordinates. It is used in [`NumberField.exists_addSubgroup_forall_finsum_units_mul_prod_zpow_neg_mul_sum_integral_discWindow_eq_tsum_mul_tsum_ite_kinkWindow_of_contDiff_of_forall_eq_of_norm_sub_le`](thm.html#NumberField.exists_addSubgroup_forall_finsum_units_mul_prod_zpow_neg_mul_sum_integral_discWindow_eq_tsum_mul_tsum_ite_kinkWindow_of_contDiff_of_forall_eq_of_norm_sub_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Complex_norm_one_sub_inv_exp_and_sq_mul_log_eq_and_contDiff.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Complex.norm_one_sub_inv_exp_and_sq_mul_log_eq_and_contDiff :
    (∀ X Θ : ℝ, ‖(1 : ℂ) - (Complex.exp (((X / 2 : ℝ) : ℂ) + 2 * Real.pi * Complex.I * (Θ : ℂ)))⁻¹‖ =
        Real.exp (-(X / 2)) * ‖(1 : ℂ) - Complex.exp (((X / 2 : ℝ) : ℂ) + 2 * Real.pi * Complex.I * (Θ : ℂ))‖) ∧
    (∀ X Θ : ℝ, ‖(1 : ℂ) - (Complex.exp (((X / 2 : ℝ) : ℂ) + 2 * Real.pi * Complex.I * (Θ : ℂ)))⁻¹‖ ^ 2 *
          Real.log ‖(1 : ℂ) - (Complex.exp (((X / 2 : ℝ) : ℂ) + 2 * Real.pi * Complex.I * (Θ : ℂ)))⁻¹‖ =
        Real.exp (-X) *
          (‖(1 : ℂ) - Complex.exp (((X / 2 : ℝ) : ℂ) + 2 * Real.pi * Complex.I * (Θ : ℂ))‖ ^ 2 *
              Real.log ‖(1 : ℂ) - Complex.exp (((X / 2 : ℝ) : ℂ) + 2 * Real.pi * Complex.I * (Θ : ℂ))‖ -
            X / 2 * ‖(1 : ℂ) - Complex.exp (((X / 2 : ℝ) : ℂ) + 2 * Real.pi * Complex.I * (Θ : ℂ))‖ ^ 2)) ∧
    (∀ X Θ : ℝ, ‖(1 : ℂ) - Complex.exp (((X / 2 : ℝ) : ℂ) + 2 * Real.pi * Complex.I * (Θ : ℂ))‖ ^ 2 =
        1 - 2 * Real.exp (X / 2) * Real.cos (2 * Real.pi * Θ) + Real.exp X) ∧
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => 1 - 2 * Real.exp (p.1 / 2) * Real.cos (2 * Real.pi * p.2) + Real.exp p.1) := by sorry
