-- Prove2me | Theorems.Thm_Arxivcond_mat_0408414_diffuse_component
-- name    : Arxivcond_mat_0408414.diffuse_component
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T19:27:09.554597+00:00
-- url     : https://prove2.me/theorems/d819e433-8e8c-4636-a05e-28948e7a0369
-- title:
--   Eq. (24): the diffuse component of the mean DRC
-- statement:
--   Let $0<H<1$, and let $\theta,\theta_0\in(-\pi/2,\pi/2)$ with $\theta\ne\theta_0$. As $s=s(\lambda)\to0^+$, the closed form (17) of the mean differential reflection coefficient satisfies
--   $$\Big\langle\frac{\partial R_s}{\partial\theta}\Big\rangle\sim\frac{\Gamma(1+2H)\sin(\pi H)}{(4\pi)^{2H-1}}\,\frac{s^2}{\cos\theta_0}\,\frac{\big|\cos\frac{\theta+\theta_0}{2}\big|^{3-2H}}{\big|\sin\frac{\theta-\theta_0}{2}\big|^{1+2H}},$$
--   that is, the ratio of the two sides tends to $1$. Away from the specular direction the mean DRC therefore decays as a power law with exponent $-1-2H$ in $|\sin\frac{\theta-\theta_0}{2}|$.
--
--   **Formalization Note** Eq. (24) is obtained by inserting the leading term of the large-argument expansion (23) of $\mathcal L_{2H}$ into (17). It is valid when the Lévy argument is large, i.e. $|\theta-\theta_0|$ large compared with the specular width. At fixed angles this is the limit $s\to0^+$, which is how "$\simeq$" is formalized. The case $H=1$ is excluded: there $\mathcal L_2$ is Gaussian and the right side is $0$.
-- source:
--   I. Simonsen, D. Vandembroucq, S. Roux, Electromagnetic wave scattering from conducting self-affine surfaces: an analytic and numerical study, arXiv:cond-mat/0408414v2, claim c009; Sec. III.B (The diffuse component), Eqs. (23)-(24), PDF p. 12

import Mathlib
import Definitions.Def_Arxivcond_mat_0408414_Basic

open MeasureTheory ProbabilityTheory Filter Topology Real Asymptotics

namespace Arxivcond_mat_0408414

theorem diffuse_component (H θ θ0 : ℝ) (hH0 : 0 < H) (hH1 : H < 1)
    (hθ : θ ∈ Set.Ioo (-(π / 2)) (π / 2)) (hθ0 : θ0 ∈ Set.Ioo (-(π / 2)) (π / 2)) (hne : θ ≠ θ0) :
    Tendsto (fun s : ℝ => mdrcFinal H s θ θ0 /
        (Real.Gamma (1 + 2 * H) * sin (π * H) / (4 * π) ^ (2 * H - 1) * (s ^ 2 / cos θ0) *
          (|cos ((θ + θ0) / 2)| ^ (3 - 2 * H) / |sin ((θ - θ0) / 2)| ^ (1 + 2 * H))))
      (𝓝[>] 0) (𝓝 1) := by sorry

end Arxivcond_mat_0408414
