-- Prove2me | Theorems.Thm_AutomorphicForm_etaFst_etaSnd_mul_normPowChar_eq_shift
-- name    : AutomorphicForm.etaFst_etaSnd_mul_normPowChar_eq_shift
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/a92b768e-26b1-5bf9-b305-450c134a67b5
-- title:
--   Twisting by ‖·‖^{iτ} shifts the η-parameter
-- statement:
--   Let $K$ be a number field, write $\mathbb{A}_K^\times$ for the unit group of the adele ring of $K$ over $\mathcal{O}_K$, and let $\alpha : \mathbb{A}_K^\times \to \mathbb{R}^\times$ be a group homomorphism such that $\alpha(x) > 0$ for all $x$ (hypothesis `hα`) and moreover $\alpha(x)$ equals the idele norm $\operatorname{ideleNorm} K\,x$, defined as the value at $x$ of the distributive Haar character of the adele ring, for all $x$ (hypothesis `_hαI`). Let $\chi : \mathbb{A}_K^\times \to \mathbb{C}^\times$ be a group homomorphism, $\tau \in \mathbb{R}$ and $s \in \mathbb{C}$. Here `cpowChar α hα s` denotes the character $x \mapsto \alpha(x)^s$, `etaFst χ α hα s` is the character $\chi \cdot \alpha^{\,s+1/2}$, `etaSnd χ α hα s` is $\chi \cdot \alpha^{-(s+1/2)}$, and `normPowChar K τ` is $x \mapsto \|x\|^{i\tau}$ with $\|x\| = \operatorname{ideleNorm} K\,x$. The assertion is a conjunction of four equalities of characters $\mathbb{A}_K^\times \to \mathbb{C}^\times$: $\eta_1(\chi\|\cdot\|^{i\tau}, s) = \eta_1(\chi, s + i\tau)$, $\eta_1(\chi\|\cdot\|^{-i\tau}, s) = \eta_1(\chi, s - i\tau)$, $\eta_2(\chi\|\cdot\|^{i\tau}, s) = \eta_2(\chi, s - i\tau)$ and $\eta_2(\chi\|\cdot\|^{-i\tau}, s) = \eta_2(\chi, s + i\tau)$, where $\eta_1 =$ `etaFst` and $\eta_2 =$ `etaSnd`, the inverse twist being the inverse in the group of characters.
--
--   This records that, for the two inducing quasi-characters attached to a spectral parameter $s$ in the Tate-style global theory, twisting the character $\chi$ by the unitary idele-norm power $\|\cdot\|^{\pm i\tau}$ is the same as translating $s$ by $\pm i\tau$, with opposite signs on the two components. It is used to re-index Paley–Wiener data along the unitary axis, for instance in [`AutomorphicForm.exists_paleyWiener_swapClosed_separated_eq_sum_of_forall_paleyWiener`](thm.html#AutomorphicForm.exists_paleyWiener_swapClosed_separated_eq_sum_of_forall_paleyWiener) and in the intertwining and inner-product identities [`AutomorphicForm.integral_mul_conj_eq_integral_axis_continuation_weylIntertwining_mul_conj_axis_continuation_weylIntertwining_of_paleyWiener_matched`](thm.html#AutomorphicForm.integral_mul_conj_eq_integral_axis_continuation_weylIntertwining_mul_conj_axis_continuation_weylIntertwining_of_paleyWiener_matched) and [`AutomorphicForm.inv_vol_sum_inner_axis_continuation_weylIntertwiningIntegral_mul_eq_self_of_swap_normPowChar`](thm.html#AutomorphicForm.inv_vol_sum_inner_axis_continuation_weylIntertwiningIntegral_mul_eq_self_of_swap_normPowChar).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_etaFst_etaSnd_mul_normPowChar_eq_shift.lean

import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_NumberField_NormPowChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.TateGlobal AutomorphicForm

theorem AutomorphicForm.etaFst_etaSnd_mul_normPowChar_eq_shift
    (K : Type) [Field K] [NumberField K]
    (α : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (_hαI : ∀ x, ((α x : ℝˣ) : ℝ) = NumberField.TateGlobal.ideleNorm K x)
    (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (τ : ℝ) (s : ℂ) :
    etaFst (χ * NumberField.TateGlobal.normPowChar K τ) α hα s = etaFst χ α hα (s + (τ : ℂ) * Complex.I) ∧
    etaFst (χ * (NumberField.TateGlobal.normPowChar K τ)⁻¹) α hα s = etaFst χ α hα (s - (τ : ℂ) * Complex.I) ∧
    etaSnd (χ * NumberField.TateGlobal.normPowChar K τ) α hα s = etaSnd χ α hα (s - (τ : ℂ) * Complex.I) ∧
    etaSnd (χ * (NumberField.TateGlobal.normPowChar K τ)⁻¹) α hα s = etaSnd χ α hα (s + (τ : ℂ) * Complex.I) := by sorry
