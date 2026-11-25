-- Prove2me | Theorems.Thm_Arxivcond_mat_0408414_specular_peak_shift
-- name    : Arxivcond_mat_0408414.specular_peak_shift
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T19:26:29.549715+00:00
-- url     : https://prove2.me/theorems/a014ec7c-5c89-411f-b20d-c50910b93a8b
-- title:
--   Eq. (22) (sign corrected): shift of the apparent specular peak
-- statement:
--   Let $0<H\le1$ with $H\ne\frac12$, and let $\theta_0\in(-\pi/2,\pi/2)$ with $\theta_0\ne0$. Put
--   $$D(s)=\frac{1-2H}{H}\,\frac{\Gamma(\frac{1}{2H})}{\Gamma(\frac{3}{2H})}\,\tan\theta_0\,\big(2\sqrt2\pi\cos\theta_0\big)^{\frac2H-2}s^{2/H}.$$
--   Then there is a choice $\theta^*(s)$ with two properties. First, for all sufficiently small $s>0$, $\theta^*(s)\in(-\pi/2,\pi/2)$ maximizes the closed form (17), $\theta\mapsto\langle\partial R_s/\partial\theta\rangle$, over $(-\pi/2,\pi/2)$. Second, the shift of this apparent specular peak satisfies
--   $$\frac{\theta^*(s)-\theta_0}{D(s)}\to1\qquad(s\to0^+).$$
--
--   **Formalization Note** The paper's Eq. (22) has the factor $\frac{2H-1}{H}$, so it claims a positive shift for $H>\frac12$ and a negative one for $H<\frac12$. Maximizing the expansion (19), whose quadratic coefficient is negative for small $s$, gives the opposite sign, $\frac{1-2H}{H}$. A direct numerical maximization of (17) confirms the opposite sign: at $H=0.7$, $\theta_0=50^\circ$, $s=0.063$ the peak is at $\theta_0-1.353\times10^{-3}$ rad. The magnitude of the printed formula is correct. The statement uses the sign that follows from (17). The paper's "$\simeq$" (with $w\ll1$) is formalized as the leading-order asymptotics as $s\to0^+$, the regime in which the peak is narrow. The cases $H=\frac12$ and $\theta_0=0$, where the leading shift vanishes, are excluded.
-- source:
--   I. Simonsen, D. Vandembroucq, S. Roux, Electromagnetic wave scattering from conducting self-affine surfaces: an analytic and numerical study, arXiv:cond-mat/0408414v2, claim c008; Sec. III.A (The specular contribution), Eq. (22) and following text, PDF pp. 11-12

import Mathlib
import Definitions.Def_Arxivcond_mat_0408414_Basic

open MeasureTheory ProbabilityTheory Filter Topology Real Asymptotics

namespace Arxivcond_mat_0408414

theorem specular_peak_shift (H θ0 : ℝ) (hH0 : 0 < H) (hH1 : H ≤ 1) (hH2 : H ≠ 1 / 2)
    (hθ0 : θ0 ∈ Set.Ioo (-(π / 2)) (π / 2)) (hθ00 : θ0 ≠ 0) :
    ∃ θstar : ℝ → ℝ,
      (∀ᶠ s in 𝓝[>] (0 : ℝ), θstar s ∈ Set.Ioo (-(π / 2)) (π / 2) ∧
        ∀ θ ∈ Set.Ioo (-(π / 2)) (π / 2), mdrcFinal H s θ θ0 ≤ mdrcFinal H s (θstar s) θ0) ∧
      Tendsto (fun s : ℝ => (θstar s - θ0) /
          ((1 - 2 * H) / H * (Real.Gamma (1 / (2 * H)) / Real.Gamma (3 / (2 * H))) * tan θ0 *
            (2 * √2 * π * cos θ0) ^ (2 / H - 2) * s ^ (2 / H)))
        (𝓝[>] 0) (𝓝 1) := by sorry

end Arxivcond_mat_0408414
