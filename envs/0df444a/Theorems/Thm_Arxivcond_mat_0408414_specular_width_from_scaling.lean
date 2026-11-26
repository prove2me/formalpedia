-- Prove2me | Theorems.Thm_Arxivcond_mat_0408414_specular_width_from_scaling
-- name    : Arxivcond_mat_0408414.specular_width_from_scaling
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T19:28:21.172868+00:00
-- url     : https://prove2.me/theorems/a3b0e48a-c1db-5403-a348-771c4d870c0d
-- title:
--   Sec. IV: the transition $\chi=1$ gives the specular width $w\simeq[2s(\lambda)]^{1/H}(\cos\theta_0)^{1/H-1}$
-- statement:
--   Let $\lambda>0$, $0<H\le1$ and $\theta_0\in(-\pi/2,\pi/2)$. Let $\chi(\theta)=\delta_{rough}/\delta_{ang}=\dfrac{(\sin\theta-\sin\theta_0)\,s^{-1/H}}{(\cos\theta+\cos\theta_0)^{1/H}}$. Then for all sufficiently small $s>0$ there is a first angle above $\theta_0$ at which $\chi=1$, namely $\theta_0+\delta(s)$ with $\delta(s)>0$, $\chi(\theta_0+\delta(s))=1$ and $\chi(\theta_0+t)<1$ for $0<t<\delta(s)$. This transition from specular peak to diffuse tail satisfies
--   $$\delta(s)\sim[2s]^{1/H}(\cos\theta_0)^{1/H-1}\qquad(s\to0^+).$$
--
--   **Formalization Note** The paper's Sec. IV is a scaling argument: "the transition between the specular peak and the diffuse tail is simply defined by $\chi=1$, which leads to $w\simeq[2s(\lambda)]^{1/H}(\cos\theta_0)^{1/H-1}$". The step uses an implicit small-angle linearization. It is formalized as the leading-order asymptotics of the first root of $\chi=1$ above $\theta_0$, as $s\to0^+$ (narrow peak). The comparison with Eq. (21) "apart from a numerical constant" is not part of the statement.
-- source:
--   I. Simonsen, D. Vandembroucq, S. Roux, Electromagnetic wave scattering from conducting self-affine surfaces: an analytic and numerical study, arXiv:cond-mat/0408414v2, claim c011; Sec. IV (Scaling analysis), definitions of δ_ang, δ_rough, χ and the width from χ = 1, PDF p. 13

import Mathlib
import Definitions.Def_Arxivcond_mat_0408414_Basic

open MeasureTheory ProbabilityTheory Filter Topology Real Asymptotics

namespace Arxivcond_mat_0408414

theorem specular_width_from_scaling (lam H θ0 : ℝ) (hlam : 0 < lam) (hH0 : 0 < H) (hH1 : H ≤ 1)
    (hθ0 : θ0 ∈ Set.Ioo (-(π / 2)) (π / 2)) :
    ∃ δ : ℝ → ℝ,
      (∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < δ s ∧ chiRatio lam H s (θ0 + δ s) θ0 = 1 ∧
        ∀ t ∈ Set.Ioo 0 (δ s), chiRatio lam H s (θ0 + t) θ0 < 1) ∧
      Tendsto (fun s : ℝ => δ s / ((2 * s) ^ (1 / H) * (cos θ0) ^ (1 / H - 1))) (𝓝[>] 0) (𝓝 1) := by sorry

end Arxivcond_mat_0408414
