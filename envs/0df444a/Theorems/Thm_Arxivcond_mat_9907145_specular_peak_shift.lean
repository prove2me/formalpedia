-- Prove2me | Theorems.Thm_Arxivcond_mat_9907145_specular_peak_shift
-- name    : Arxivcond_mat_9907145.specular_peak_shift
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T19:32:19.985354+00:00
-- url     : https://prove2.me/theorems/a723f167-bbd8-54ee-b825-46499e3ee1ed
-- title:
--   Eq. (17) (sign corrected): shift of the specular peak
-- statement:
--   Let $0<H<1$ with $H\ne\frac12$, and let $\theta_0\in(-\pi/2,\pi/2)$ with $\theta_0\ne0$. Put
--   $$D(r)=\frac{1-2H}{H}\,\frac{\Gamma(\frac1{2H})}{\Gamma(\frac3{2H})}\,\tan\theta_0\,\Big(2\sqrt2\pi r\cos\theta_0\Big)^{\frac2H-2}.$$
--   Then there is a choice $\theta^*(r)$ with two properties. First, for all sufficiently small $r=\ell/\lambda>0$, $\theta^*(r)\in(-\pi/2,\pi/2)$ maximizes the closed form (14a) over $\theta\in(-\pi/2,\pi/2)$. Second, the shift $\Delta\theta_0=\theta^*(r)-\theta_0$ of the specular peak satisfies
--   $$\frac{\theta^*(r)-\theta_0}{D(r)}\to1\qquad(r\to0^+).$$
--   This is Eq. (17) with its sign corrected: the peak sits at $\theta_0+\Delta\theta_0$ with $\Delta\theta_0\simeq D$, a shift of order $w^2\ll w$.
--
--   **Formalization Note** The paper's "$\simeq$" under the assumption $\frac\omega c\ell\cos\theta_0\ll1$ is formalized as the leading-order asymptotics as $r\to0^+$, the regime in which the peak is narrow. The peak is the global maximizer of (14a). $H<1$ is needed because for $H=1$ the closed form does not depend on $r$. $H=\frac12$ and $\theta_0=0$ are excluded because $D=0$ there. The paper prints the factor $\frac{2H-1}{H}$; this sign is wrong. At $\theta=\theta_0$ the derivative of $\log$ (14a) is $\frac{1-2H}{2H}\tan\theta_0$, and the second-order expansion about $\theta_0$ gives the factor $\frac{1-2H}{H}$. Direct maximization of (14a) gives $(\theta^*-\theta_0)/D_{\rm printed}\approx-1.023,-1.003$ at $H=0.7$, $\theta_0=50^\circ$, $r=10^{-3},10^{-4}$, and $\approx-1.001,-1.000$ at $H=0.3$, $r=0.1,0.03$. The magnitude and the $w^2$ scaling of the printed formula are right; only the sign is changed here.
-- source:
--   I. Simonsen, D. Vandembroucq, S. Roux, Wave scattering from self-affine surfaces, arXiv:cond-mat/9907145v1, claim c014; main text, Eq. (17) and preceding sentence, PDF p. 3

import Mathlib
import Definitions.Def_Arxivcond_mat_9907145_Basic

open MeasureTheory ProbabilityTheory Filter Topology Real

namespace Arxivcond_mat_9907145

theorem specular_peak_shift (H θ0 : ℝ) (hH0 : 0 < H) (hH1 : H < 1) (hH2 : H ≠ 1 / 2)
    (hθ0 : θ0 ∈ Set.Ioo (-(π / 2)) (π / 2)) (hθ00 : θ0 ≠ 0) :
    ∃ θstar : ℝ → ℝ,
      (∀ᶠ r in 𝓝[>] (0 : ℝ), θstar r ∈ Set.Ioo (-(π / 2)) (π / 2) ∧
        ∀ θ ∈ Set.Ioo (-(π / 2)) (π / 2), mdrcFinal H r θ θ0 ≤ mdrcFinal H r (θstar r) θ0) ∧
      Tendsto (fun r : ℝ => (θstar r - θ0) /
          ((1 - 2 * H) / H * (Real.Gamma (1 / (2 * H)) / Real.Gamma (3 / (2 * H))) * tan θ0 *
            (2 * √2 * π * r * cos θ0) ^ (2 / H - 2)))
        (𝓝[>] 0) (𝓝 1) := by sorry

end Arxivcond_mat_9907145
