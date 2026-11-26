-- Prove2me | Theorems.Thm_Arxiv2401_10389_multi_angle_least_squares
-- name    : Arxiv2401_10389.multi_angle_least_squares
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-26T13:15:58.114069+00:00
-- url     : https://prove2.me/theorems/2613a5e3-f89b-5d28-8847-cdc49ba442cd
-- title:
--   Eqs. (16)-(18): multiple transmit angles reduce to the stacked system $s_\theta\approx K_\theta(\Gamma,u_0)u$, solved as in eq. (15) (as proved)
-- statement:
--   Let $N_e\ge1$ and $N_\theta\ge1$. Fix transmit delays $\tau_n(\theta)$ for $N_\theta$ transmit angles and the central frequency $\omega_0$, and let $T_\theta=T\circ A(\theta)$ with $A_n(\omega_0,\theta)=e^{i\omega_0\tau_n(\theta)}$. Assume the aberration $u$ is the same for every angle. Let $s_\theta(u)$ be the vectorized multi-angle model signal, whose block for angle $\theta$ is $\hat M(\Gamma,u)$ computed with $T_\theta$. Let $K_\theta(\Gamma,u_0)$ be the vertical stack of the operators $K_1(\Gamma,u_0),\dots,K_{N_\theta}(\Gamma,u_0)$ of eq. (13a) built with $T_1,\dots,T_{N_\theta}$. Then:
--
--   1. For every $u$, block $\theta$ of $K_\theta(\Gamma,u_0)(u\,|\,1)^T$ equals $\hat M_\theta(\Gamma,u_0)+\nabla_u\hat M_\theta(\Gamma,u_0)(u-u_0)$.
--   2. To first order, $s_\theta(u)=K_\theta(\Gamma,u_0)(u\,|\,1)^T+o(\|u-u_0\|)$ as $u\to u_0$.
--   3. For every vectorized measurement $s_\theta\in\mathbb{C}^{N_\theta N_e}$ and every $\alpha>0$ for which $K_\theta^\dagger K_\theta+\alpha D_2^TD_2$ is invertible ($D_2$ of size $N_e+1$), the unique minimiser of $\|s_\theta-K_\theta v\|^2+\alpha\|D_2v\|^2$ over $v\in\mathbb{C}^{N_e+1}$ is
--   $$\hat u=(K_\theta^\dagger K_\theta+\alpha D_2^TD_2)^{-1}K_\theta^\dagger s_\theta,$$
--   the same form as eq. (15).
--
--   This is the form of the method used in the paper's experiments, which use 11 compounding angles.
--
--   **Formalization Note** The paper writes "$s_\theta=K_\theta(\Gamma,u_0)u$" in eq. (17) with an equality sign. The single-angle relation it generalises, eq. (12), is only a first-order approximation, and the reduction establishes no more than that. Part 2 therefore states the approximation as a little-$o$ remainder (the title says "as proved"). The invertibility of the normal matrix is implicit in the paper and is a hypothesis here.
-- source:
--   Xing, Malescot, Martineau, Rungta and Provost, Inverse Problem Approach to Aberration Correction for in vivo Transcranial Imaging Based on a Sparse Representation of Contrast-enhanced Ultrasound Data, arXiv:2401.10389v3 (2025), claim c005; Section II.D, eqs. (16), (17), (18), PDF p. 4

import Mathlib
import Definitions.Def_Arxiv2401_10389_Basic

open Matrix Filter Topology Asymptotics

namespace Arxiv2401_10389

theorem multi_angle_least_squares {Ne Ns Nθ : ℕ} (hNe : 1 ≤ Ne) (hNθ : 1 ≤ Nθ)
    (R : Matrix (Fin Ne) (Fin Ns) ℂ) (γ : Fin Ns → ℂ) (T : Matrix (Fin Ne) (Fin Ns) ℂ)
    (ω₀ : ℝ) (τ : Fin Nθ → Fin Ne → ℝ) (u₀ : Fin Ne → ℂ) :
    (∀ u : Fin Ne → ℂ, multiAngleOperator R γ T ω₀ τ u₀ *ᵥ augment u =
      fun x => (forwardModel R γ (angleTransmit T ω₀ τ x.1) u₀ +
        forwardGradient R γ (angleTransmit T ω₀ τ x.1) u₀ *ᵥ (u - u₀)) x.2) ∧
    ((fun u => multiAngleSignal R γ T ω₀ τ u - multiAngleOperator R γ T ω₀ τ u₀ *ᵥ augment u)
      =o[𝓝 u₀] (fun u => u - u₀)) ∧
    (∀ (sθ : Fin Nθ × Fin Ne → ℂ) (α : ℝ), 0 < α →
      (normalMatrix (multiAngleOperator R γ T ω₀ τ u₀) (secondDiffMatrix (Ne + 1)) α).det ≠ 0 →
      {v : Fin (Ne + 1) → ℂ | ∀ w, tikhonovObjective (multiAngleOperator R γ T ω₀ τ u₀)
          (secondDiffMatrix (Ne + 1)) α sθ v ≤
        tikhonovObjective (multiAngleOperator R γ T ω₀ τ u₀) (secondDiffMatrix (Ne + 1)) α sθ w} =
      {tikhonovSolution (multiAngleOperator R γ T ω₀ τ u₀) (secondDiffMatrix (Ne + 1)) α sθ}) := by sorry

end Arxiv2401_10389
