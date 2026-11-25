-- Prove2me | Theorems.Thm_Arxivcond_mat_0408414_specular_expansion
-- name    : Arxivcond_mat_0408414.specular_expansion
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T19:25:44.364432+00:00
-- url     : https://prove2.me/theorems/881c1f04-4706-5ec5-bcd9-318683b17e16
-- title:
--   Eq. (19) (as corrected): second-order expansion of the mean DRC around the specular direction
-- statement:
--   Let $s>0$, $0<H\le1$, $\theta_0\in(-\pi/2,\pi/2)$, and let $A$ be the specular amplitude of Eq. (20). Put $X=(2\sqrt2\pi\cos\theta_0)^{2/H-2}s^{2/H}$. As $\delta\theta\to0$, the closed form (17) satisfies
--   $$\Big\langle\frac{\partial R_s}{\partial\theta}\Big\rangle\Big|_{\theta_0+\delta\theta}=A\Big[1+\delta\theta\,\frac{1-2H}{2H}\tan\theta_0+\frac{(\delta\theta)^2}{4}\Big(\frac1H+\frac{(1-2H)(1-H)}{2H^2}\tan^2\theta_0-\frac{\Gamma(\frac{3}{2H})}{\Gamma(\frac{1}{2H})\,X}\Big)\Big]+o\big((\delta\theta)^2\big).$$
--
--   **Formalization Note** This is Eq. (19) with a corrected $s$-independent part of the quadratic coefficient. The paper prints $1+\frac{1+H}{2H^2}\tan^2\theta_0$ there. Substituting the expansion (18) of $\mathcal L_{2H}$ into (17), which is the paper's own method, gives $\frac1H+\frac{(1-2H)(1-H)}{2H^2}\tan^2\theta_0$; for example at $\theta_0=0$ the term is $1/H$, not $1$. The amplitude $A$, the linear coefficient and the $s$-dependent quadratic term are as printed. The expansion "$\delta\theta\ll1$" is formalized with an $o((\delta\theta)^2)$ remainder.
-- source:
--   I. Simonsen, D. Vandembroucq, S. Roux, Electromagnetic wave scattering from conducting self-affine surfaces: an analytic and numerical study, arXiv:cond-mat/0408414v2, claim c004; Sec. III.A (The specular contribution), Eqs. (18)-(19), PDF p. 10

import Mathlib
import Definitions.Def_Arxivcond_mat_0408414_Basic

open MeasureTheory ProbabilityTheory Filter Topology Real Asymptotics

namespace Arxivcond_mat_0408414

theorem specular_expansion (H s θ0 : ℝ) (hs : 0 < s) (hH0 : 0 < H) (hH1 : H ≤ 1)
    (hθ0 : θ0 ∈ Set.Ioo (-(π / 2)) (π / 2)) :
    (fun δ : ℝ => mdrcFinal H s (θ0 + δ) θ0 -
      Real.Gamma (1 / (2 * H)) /
          (2 * √2 * π * H * (2 * √2 * π * cos θ0) ^ (1 / H - 1) * s ^ (1 / H)) *
        (1 + δ * ((1 - 2 * H) / (2 * H)) * tan θ0 +
          δ ^ 2 / 4 * (1 / H + (1 - 2 * H) * (1 - H) / (2 * H ^ 2) * tan θ0 ^ 2 -
            Real.Gamma (3 / (2 * H)) /
              (Real.Gamma (1 / (2 * H)) * (2 * √2 * π * cos θ0) ^ (2 / H - 2) * s ^ (2 / H)))))
      =o[𝓝 0] (fun δ : ℝ => δ ^ 2) := by sorry

end Arxivcond_mat_0408414
