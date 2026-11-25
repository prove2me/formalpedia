-- Prove2me | Theorems.Thm_Arxivcond_mat_9907145_specular_peak_amplitude
-- name    : Arxivcond_mat_9907145.specular_peak_amplitude
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T19:31:54.871005+00:00
-- url     : https://prove2.me/theorems/6488bf43-b77c-4171-ad14-23affb74cafc
-- title:
--   Eq. (15): amplitude of the specular peak
-- statement:
--   Let $r=\ell/\lambda>0$, $0<H\le1$ and $\theta_0\in(-\pi/2,\pi/2)$. The closed form (14a) of the mean differential reflection coefficient at the specular angle $\theta=\theta_0$ is
--   $$\Big\langle\frac{\partial R}{\partial\theta}\Big\rangle\Big|_{\theta=\theta_0}=\frac{\Gamma(\frac1{2H})}{2\sqrt2\pi H\big(2\sqrt2\pi\frac\ell\lambda\cos\theta_0\big)^{1/H-1}} .$$
--   It follows from $\mathcal L_\alpha(0)=\Gamma(1/\alpha)/(\pi\alpha)$ with $\alpha=2H$.
--
--   **Formalization Note** The paper prints "$\simeq$". At exactly $\theta=\theta_0$ the value of (14a) is this expression with no error term, so it is stated as an equality. The maximum of the peak is slightly displaced from $\theta_0$; see `specular_peak_shift`.
-- source:
--   I. Simonsen, D. Vandembroucq, S. Roux, Wave scattering from self-affine surfaces, arXiv:cond-mat/9907145v1, claim c012; main text, Eq. (15) and footnote [27], PDF p. 3

import Mathlib
import Definitions.Def_Arxivcond_mat_9907145_Basic

open MeasureTheory ProbabilityTheory Filter Topology Real

namespace Arxivcond_mat_9907145

theorem specular_peak_amplitude (H r θ0 : ℝ) (hr : 0 < r) (hH0 : 0 < H) (hH1 : H ≤ 1)
    (hθ0 : θ0 ∈ Set.Ioo (-(π / 2)) (π / 2)) :
    mdrcFinal H r θ0 θ0 =
      Real.Gamma (1 / (2 * H)) / (2 * √2 * π * H * (2 * √2 * π * r * cos θ0) ^ (1 / H - 1)) := by sorry

end Arxivcond_mat_9907145
