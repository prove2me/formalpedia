-- Prove2me | Theorems.Thm_Arxivcond_mat_9907145_diffuse_tail
-- name    : Arxivcond_mat_9907145.diffuse_tail
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T19:33:12.30816+00:00
-- url     : https://prove2.me/theorems/559080c9-d3ce-544e-a80e-bee7c287b936
-- title:
--   Unnumbered equation after the dimensional argument: power-law diffuse tail of the mean DRC
-- statement:
--   Let $0<H<1$ and $\theta,\theta_0\in(-\pi/2,\pi/2)$ with $\theta\ne\theta_0$. As $r=\ell/\lambda\to0^+$, the closed form (14a) of the mean differential reflection coefficient satisfies
--   $$\Big\langle\frac{\partial R}{\partial\theta}\Big\rangle\sim\frac{\Gamma(1+2H)\sin(\pi H)}{4\pi}\,\frac{\big(4\pi\frac\ell\lambda\big)^{2-2H}\big(\cos\frac{\theta+\theta_0}{2}\big)^{3-2H}}{\cos\theta_0\,\big|\sin\frac{\theta-\theta_0}{2}\big|^{1+2H}},$$
--   that is, the ratio of the two sides tends to $1$. Away from the specular direction the diffuse intensity decays as a power law in $|\sin\frac{\theta-\theta_0}{2}|$ with exponent $1+2H$, with a prefactor that depends explicitly on $\ell$ and $H$.
--
--   **Formalization Note** The formula comes from inserting the large-argument expansion $\mathcal L_\alpha(x)\simeq\Gamma(1+\alpha)\sin(\alpha\pi/2)/(\pi|x|^{1+\alpha})$ (footnote [28]) into (14a). It is valid when the Lévy argument is large, which at fixed $\theta\ne\theta_0$ is the limit $\ell/\lambda\to0^+$; this is how "$\simeq$" is formalized. $H=1$ is excluded: there $\sin\pi H=0$ and $\mathcal L_2$ is Gaussian. The paper's remark that the power law survives in a non-perturbative approach is an interpretation, not a separate statement.
-- source:
--   I. Simonsen, D. Vandembroucq, S. Roux, Wave scattering from self-affine surfaces, arXiv:cond-mat/9907145v1, claim c017; main text, unnumbered equation after the dimensional-argument paragraph and footnote [28], PDF p. 4

import Mathlib
import Definitions.Def_Arxivcond_mat_9907145_Basic

open MeasureTheory ProbabilityTheory Filter Topology Real

namespace Arxivcond_mat_9907145

theorem diffuse_tail (H θ θ0 : ℝ) (hH0 : 0 < H) (hH1 : H < 1)
    (hθ : θ ∈ Set.Ioo (-(π / 2)) (π / 2)) (hθ0 : θ0 ∈ Set.Ioo (-(π / 2)) (π / 2)) (hne : θ ≠ θ0) :
    Tendsto (fun r : ℝ => mdrcFinal H r θ θ0 /
        (Real.Gamma (1 + 2 * H) * sin (π * H) / (4 * π) *
          ((4 * π * r) ^ (2 - 2 * H) * cos ((θ + θ0) / 2) ^ (3 - 2 * H)) /
          (cos θ0 * |sin ((θ - θ0) / 2)| ^ (1 + 2 * H))))
      (𝓝[>] 0) (𝓝 1) := by sorry

end Arxivcond_mat_9907145
