-- Prove2me | Theorems.Thm_Arxiv1110_5134_layered_clausius_invariant
-- name    : Arxiv1110_5134.layered_clausius_invariant
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T08:59:09.9706+00:00
-- url     : https://prove2.me/theorems/454534ed-47a2-4217-8e90-0f6c1c81fad9
-- title:
--   Eq. (7): intensity over $n^2$ is preserved across a layer interface
-- statement:
--   Let two adjacent layers have refractive indices $n_1,n_2>0$. A beam crosses from layer 1 to layer 2 with zenith angle $\theta_1\in(0,\pi/2)$, and the transmitted zenith angle $\theta_2=\theta_2(\theta_1)$ is given near $\theta_1$ by Snell's law $n_1\sin\theta_1=n_2\sin\theta_2$. Suppose $\theta_2$ is differentiable at $\theta_1$. Energy is conserved across the interface (Eqs. 4-5):
--
--   $$I_1\cos\theta_1\sin\theta_1\,d\theta_1=I_2\cos\theta_2\sin\theta_2\,d\theta_2 ,$$
--
--   with the azimuth unchanged by refraction. Then Snell's law takes the differential form (Eq. 6)
--
--   $$n_1^2\,d\cos^2\theta_1=n_2^2\,d\cos^2\theta_2,$$
--
--   and the intensities satisfy (Eq. 7)
--
--   $$\frac{I_1}{n_1^2}=\frac{I_2}{n_2^2}.$$
--
--   **Formalization Note** The differentials are derivatives with respect to $\theta_1$, so energy conservation reads $I_1\cos\theta_1\sin\theta_1=I_2\cos\theta_2\sin\theta_2\,\theta_2'(\theta_1)$. The paper's further limit of vanishing index steps, which gives Eq. (3), is not part of this statement.
-- source:
--   Zhao, Tan and Liu, On the Derivation of Vector Radiative Transfer Equation for Polarized Radiative Transport in Graded Index Media, arXiv:1110.5134v1 (2011), claim c001; Section 2.3, Eqs. (4)-(7), PDF pp. 7-8

import Mathlib
import Definitions.Def_Arxiv1110_5134_Basic

open MeasureTheory Filter Topology
open scoped Matrix

namespace Arxiv1110_5134

theorem layered_clausius_invariant (n₁ n₂ I₁ I₂ θ₁ θ₂' : ℝ) (θ₂ : ℝ → ℝ)
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (hθ₁ : θ₁ ∈ Set.Ioo 0 (Real.pi / 2))
    (hsnell : ∀ᶠ t in 𝓝 θ₁, n₁ * Real.sin t = n₂ * Real.sin (θ₂ t))
    (hθ₂ : HasDerivAt θ₂ θ₂' θ₁)
    (henergy : I₁ * Real.cos θ₁ * Real.sin θ₁ =
      I₂ * Real.cos (θ₂ θ₁) * Real.sin (θ₂ θ₁) * θ₂') :
    HasDerivAt (fun t => n₂ ^ 2 * Real.cos (θ₂ t) ^ 2)
      (n₁ ^ 2 * (-(2 * Real.cos θ₁ * Real.sin θ₁))) θ₁ ∧
    I₁ / n₁ ^ 2 = I₂ / n₂ ^ 2 := by sorry

end Arxiv1110_5134
