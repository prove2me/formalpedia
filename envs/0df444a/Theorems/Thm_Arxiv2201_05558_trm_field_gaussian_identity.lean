-- Prove2me | Theorems.Thm_Arxiv2201_05558_trm_field_gaussian_identity
-- name    : Arxiv2201_05558.trm_field_gaussian_identity
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T10:53:27.908729+00:00
-- url     : https://prove2.me/theorems/7569892e-8919-5111-86a5-09a20278223a
-- title:
--   Eq. (3.4)-(3.5): the time-reversed field of a Gaussian mirror with Gaussian elements
-- statement:
--   Let $c_o,\omega,\tilde\omega,R_m,\rho_0>0$ and $r_0=\sqrt{R_m^2+\rho_0^2}$. Let $G_1,G_2:\mathbb{R}^2\to\mathbb{C}$ be measurable: $G_1$ is the emitting Green's function $\mathcal G(\omega,L,x,\cdot)$ and $G_2$ the recording one $\mathcal G(\tilde\omega,L,y,\cdot)$. Assume that $(x_m,x',x'')\mapsto G_1(x_m+x')\overline{G_2(x_m+x'')}e^{-|x'|^2/(2\rho_0^2)-|x''|^2/(2\rho_0^2)-|x_m|^2/R_m^2}$ is integrable on $(\mathbb{R}^2)^3$. Define
--
--   $$\hat u_{\rm rec}(x_m)=\frac{1}{2\pi\rho_0^2}\int G_2(x_m+x')e^{-\frac{|x'|^2}{2\rho_0^2}}dx',\qquad \hat u_{\rm em}(x_m)=\frac{1}{2\pi\rho_0^2}\int G_1(x_m+x')e^{-\frac{|x'|^2}{2\rho_0^2}}dx',$$
--
--   $$\hat u_{\rm tr}=\int\hat u_{\rm em}(x_m)\,e^{-|x_m|^2/R_m^2}\,\overline{\hat u_{\rm rec}(x_m)}\,dx_m.$$
--
--   Then, with $K_0=\frac{c_o^2(r_0^2-\rho_0^2)}{16\pi\omega\tilde\omega\rho_0^2r_0^2}$,
--
--   $$\hat u_{\rm tr}=\frac{4\omega\tilde\omega}{c_o^2}K_0\iint\exp\Big(-\frac{|x'|^2}{r_0^2}-\frac{|y'|^2}{4\rho_0^2}\Big)G_1\big(x'+\tfrac{y'}{2}\big)\overline{G_2\big(x'-\tfrac{y'}{2}\big)}\,dx'\,dy'.$$
--
--   This is the form of the time-reversed field that the rest of the paper works with.
--
--   **Formalization Note** The identity holds for any fields $G_1,G_2$ for which the integrals converge absolutely, so the Green's functions are arbitrary measurable functions subject to that integrability hypothesis; the paper leaves convergence implicit. The broadband analogue (3.9) is not part of this statement.
-- source:
--   Garnier and Sølna, Speckle Memory Effect in the Frequency Domain and Stability in Time-Reversal Experiments, arXiv:2201.05558v1 (2022), claim c087; Section 3.1, eqs. (3.1)-(3.5), PDF p. 7

import Mathlib
import Definitions.Def_Arxiv2201_05558_Basic

open MeasureTheory Filter Topology

namespace Arxiv2201_05558

theorem trm_field_gaussian_identity (c0 ω ωt Rm ρ0 r0 : ℝ) (hc0 : 0 < c0) (hω : 0 < ω)
    (hωt : 0 < ωt) (hRm : 0 < Rm) (hρ0 : 0 < ρ0) (hr0 : 0 < r0)
    (hr0sq : r0 ^ 2 = Rm ^ 2 + ρ0 ^ 2) (G1 G2 : Plane → ℂ)
    (hG1 : AEStronglyMeasurable G1 volume) (hG2 : AEStronglyMeasurable G2 volume)
    (hint : Integrable (fun p : Plane × Plane × Plane =>
      G1 (p.1 + p.2.1) * starRingEnd ℂ (G2 (p.1 + p.2.2)) *
        (Real.exp (-‖p.2.1‖ ^ 2 / (2 * ρ0 ^ 2) - ‖p.2.2‖ ^ 2 / (2 * ρ0 ^ 2) -
          ‖p.1‖ ^ 2 / Rm ^ 2) : ℂ))) :
    trField Rm ρ0 G1 G2 =
      ((4 * ω * ωt / c0 ^ 2 * K0 c0 ω ωt r0 ρ0 : ℝ) : ℂ) *
        ∫ X : Plane, ∫ Y : Plane,
          (Real.exp (-‖X‖ ^ 2 / r0 ^ 2 - ‖Y‖ ^ 2 / (4 * ρ0 ^ 2)) : ℂ) *
            G1 (X + (1 / 2 : ℝ) • Y) * starRingEnd ℂ (G2 (X - (1 / 2 : ℝ) • Y)) := by sorry

end Arxiv2201_05558
