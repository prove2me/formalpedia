-- Prove2me | Theorems.Thm_Arxivcond_mat_0408414_specular_peak_amplitude
-- name    : Arxivcond_mat_0408414.specular_peak_amplitude
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T19:25:18.466482+00:00
-- url     : https://prove2.me/theorems/3dcb0399-b962-56d1-953d-125542aff4e2
-- title:
--   Eq. (20): amplitude of the specular peak
-- statement:
--   Let $s>0$, $0<H\le1$ and $\theta_0\in(-\pi/2,\pi/2)$. The closed form (17) of the mean differential reflection coefficient, evaluated at the specular angle $\theta=\theta_0$, is
--   $$\Big\langle\frac{\partial R_s}{\partial\theta}\Big\rangle\Big|_{\theta=\theta_0}=\frac{\Gamma\big(\frac{1}{2H}\big)}{2\sqrt2\,\pi H\,\big(2\sqrt2\,\pi\cos\theta_0\big)^{\frac1H-1}s^{1/H}}.$$
--   In particular it scales as $s(\lambda)^{-1/H}$.
--
--   **Formalization Note** The paper writes $\simeq$. The formula is exact for Eq. (17) at $\theta=\theta_0$, because $\mathcal L_{2H}(0)=\Gamma(1/(2H))/(2\pi H)$, so it is stated as an equality. It is the value at $\theta=\theta_0$, not at the slightly shifted maximum (see Eq. (22)).
-- source:
--   I. Simonsen, D. Vandembroucq, S. Roux, Electromagnetic wave scattering from conducting self-affine surfaces: an analytic and numerical study, arXiv:cond-mat/0408414v2, claim c005; Sec. III.A (The specular contribution), Eq. (20), PDF p. 10

import Mathlib
import Definitions.Def_Arxivcond_mat_0408414_Basic

open MeasureTheory ProbabilityTheory Filter Topology Real Asymptotics

namespace Arxivcond_mat_0408414

theorem specular_peak_amplitude (H s θ0 : ℝ) (hs : 0 < s) (hH0 : 0 < H) (hH1 : H ≤ 1)
    (hθ0 : θ0 ∈ Set.Ioo (-(π / 2)) (π / 2)) :
    mdrcFinal H s θ0 θ0 =
      Real.Gamma (1 / (2 * H)) /
        (2 * √2 * π * H * (2 * √2 * π * cos θ0) ^ (1 / H - 1) * s ^ (1 / H)) := by sorry

end Arxivcond_mat_0408414
