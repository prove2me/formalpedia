-- Prove2me | Theorems.Thm_Arxiv2401_10389_linearized_forward_model
-- name    : Arxiv2401_10389.linearized_forward_model
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-26T13:15:01.295029+00:00
-- url     : https://prove2.me/theorems/7b686a93-91eb-491f-87ae-4e6bc51d07e0
-- title:
--   Eqs. (11)-(13): first-order linearization $s\approx K(\Gamma,u_0)(u\,|\,1)^T$
-- statement:
--   In the setting of eq. (6), fix an arbitrary reference aberration $u_0\in\mathbb{C}^{N_e}$ and let $K(\Gamma,u_0)=\big(\nabla_u\hat M(\Gamma,u_0)\,\big|\,\hat M(\Gamma,u_0)-\nabla_u\hat M(\Gamma,u_0)u_0\big)$. Then:
--
--   1. For every $u\in\mathbb{C}^{N_e}$, $K(\Gamma,u_0)\,(u\,|\,1)^T=\hat M(\Gamma,u_0)+\nabla_u\hat M(\Gamma,u_0)(u-u_0)$.
--   2. This is the first-order Taylor expansion of the forward model at $u_0$:
--   $$\hat M(\Gamma,u)-K(\Gamma,u_0)\,(u\,|\,1)^T=o(\|u-u_0\|)\qquad(u\to u_0).$$
--   So a signal $s=\hat M(\Gamma,u)$ satisfies $s\approx K(\Gamma,u_0)(u\,|\,1)^T$, eqs. (11)-(12).
--   3. For $u_0=\mathbf 1$, $\hat M(\Gamma,\mathbf 1)$ is the aberration-free signal of eq. (2): $\hat M_m(\Gamma,\mathbf 1)=\sum_s\sum_nR_{m,s}\Gamma_{s,s}T_{n,s}$.
--
--   The linear system $s\approx Ku$ is what the inverse problem of Section II.C inverts.
--
--   **Formalization Note** The paper's "$\approx$" in eqs. (11)-(12) is formalized as the little-$o$ remainder of a first-order Taylor expansion, for a signal produced by the forward model. The paper gives no quantitative error bound. The exact identity of part 1 is the content of eq. (13).
-- source:
--   Xing, Malescot, Martineau, Rungta and Provost, Inverse Problem Approach to Aberration Correction for in vivo Transcranial Imaging Based on a Sparse Representation of Contrast-enhanced Ultrasound Data, arXiv:2401.10389v3 (2025), claim c026; Section II.B, eqs. (11), (12), (13a), (13b), PDF pp. 3-4

import Mathlib
import Definitions.Def_Arxiv2401_10389_Basic

open Matrix Filter Topology Asymptotics

namespace Arxiv2401_10389

theorem linearized_forward_model {Ne Ns : ℕ} (R : Matrix (Fin Ne) (Fin Ns) ℂ) (γ : Fin Ns → ℂ)
    (T : Matrix (Fin Ne) (Fin Ns) ℂ) (u₀ : Fin Ne → ℂ) :
    (∀ u : Fin Ne → ℂ, linearOperator R γ T u₀ *ᵥ augment u =
      forwardModel R γ T u₀ + forwardGradient R γ T u₀ *ᵥ (u - u₀)) ∧
    ((fun u => forwardModel R γ T u - linearOperator R γ T u₀ *ᵥ augment u)
      =o[𝓝 u₀] (fun u => u - u₀)) ∧
    forwardModel R γ T (fun _ => 1) = unaberratedSignal R γ T := by sorry

end Arxiv2401_10389
