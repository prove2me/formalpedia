-- Prove2me | Theorems.Thm_Arxivcond_mat_9907145_kirchhoff_mdrc_reduction
-- name    : Arxivcond_mat_9907145.kirchhoff_mdrc_reduction
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T19:29:58.128876+00:00
-- url     : https://prove2.me/theorems/f8868601-3b48-4c3a-885d-09cbfb679349
-- title:
--   Eqs. (8)-(11): the Kirchhoff mean DRC depends on the surface only through $\Omega(v)$
-- statement:
--   Let $K=\omega/c>0$ and $\theta,\theta_0\in(-\pi/2,\pi/2)$. Let $\zeta$ be a random profile on a probability space: jointly measurable in the realization and $x$, with $C^1$ sample paths, and with stationary increments, i.e. the law of $\zeta(x)-\zeta(x+v)$ does not depend on $x$. Let $\Omega(v)$ be the characteristic function (11) of the increment at $K(\cos\theta+\cos\theta_0)$, and assume $\Omega$ is integrable on $\mathbb R$. Let $\langle\partial R/\partial\theta\rangle_L$ be the mean differential reflection coefficient (8) built from the Kirchhoff amplitude (9) of the profile on $|x|\le L/2$. Then, as $L\to\infty$,
--   $$\Big\langle\frac{\partial R}{\partial\theta}\Big\rangle_L-\frac{\omega}{2\pi c}\frac{1}{\cos\theta_0}\frac{\cos^2\frac{\theta+\theta_0}{2}}{\cos^2\frac{\theta-\theta_0}{2}}\int_{-L/2}^{L/2}e^{i\frac\omega c(\sin\theta-\sin\theta_0)v}\,\Omega(v)\,dv\;\to\;0,$$
--   and
--   $$\Big\langle\frac{\partial R}{\partial\theta}\Big\rangle_L\to\frac{\omega}{2\pi c}\frac{1}{\cos\theta_0}\frac{\cos^2\frac{\theta+\theta_0}{2}}{\cos^2\frac{\theta-\theta_0}{2}}\int_{-\infty}^{\infty}e^{i\frac\omega c(\sin\theta-\sin\theta_0)v}\,\Omega(v)\,dv .$$
--   So the surface statistics enter the mean DRC only through $\Omega$.
--
--   **Formalization Note** The paper presents Eq. (10) at finite $L$. That is exact only in the limit: the double integral over $x,x'$ gives the weight $(1-|v|/L)$ on $(-L,L)$, and eliminating $\zeta'$ by parts leaves boundary terms. Both effects vanish as $L\to\infty$, which is how (10) is used to reach (14). The statement therefore compares (8) with (10) as $L\to\infty$. Three hypotheses are not in the paper. $C^1$ paths make $\zeta'$ in the source function meaningful; the paper ensures this through the lower cut-off $\xi_-$. Joint measurability makes the expectation meaningful. Integrability of $\Omega$ makes the $L\to\infty$ limit exist. Stationary increments are taken in law, which is how the paper uses them.
-- source:
--   I. Simonsen, D. Vandembroucq, S. Roux, Wave scattering from self-affine surfaces, arXiv:cond-mat/9907145v1, claim c001; main text (unsectioned letter), Eqs. (8)-(11), PDF p. 3

import Mathlib
import Definitions.Def_Arxivcond_mat_9907145_Basic

open MeasureTheory ProbabilityTheory Filter Topology Real

namespace Arxivcond_mat_9907145

theorem kirchhoff_mdrc_reduction {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ζ : Ω → ℝ → ℝ) (K θ θ0 : ℝ) (hK : 0 < K)
    (hθ : θ ∈ Set.Ioo (-(π / 2)) (π / 2)) (hθ0 : θ0 ∈ Set.Ioo (-(π / 2)) (π / 2))
    (hmeas : Measurable (Function.uncurry ζ)) (hC1 : ∀ ω, ContDiff ℝ 1 (ζ ω))
    (hstat : ∀ x v : ℝ, P.map (fun ω => ζ ω x - ζ ω (x + v)) = P.map (fun ω => ζ ω 0 - ζ ω v))
    (hint : Integrable (fun v => incrementCF P ζ K θ θ0 v)) :
    Tendsto (fun L : ℝ => (meanDRC P ζ K θ θ0 L : ℂ) -
        kirchhoffMDRC K θ θ0 L (fun v => incrementCF P ζ K θ θ0 v)) atTop (𝓝 0) ∧
    Tendsto (fun L : ℝ => (meanDRC P ζ K θ θ0 L : ℂ)) atTop
      (𝓝 (((K / (2 * π) * (1 / cos θ0) * (cos ((θ + θ0) / 2) ^ 2 / cos ((θ - θ0) / 2) ^ 2) : ℝ) : ℂ) *
        ∫ v, Complex.exp (((K * (sin θ - sin θ0) * v : ℝ) : ℂ) * Complex.I) *
          incrementCF P ζ K θ θ0 v)) := by sorry

end Arxivcond_mat_9907145
