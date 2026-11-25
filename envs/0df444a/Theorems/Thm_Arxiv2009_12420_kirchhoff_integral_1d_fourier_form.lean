-- Prove2me | Theorems.Thm_Arxiv2009_12420_kirchhoff_integral_1d_fourier_form
-- name    : Arxiv2009_12420.kirchhoff_integral_1d_fourier_form
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T09:14:20.440931+00:00
-- url     : https://prove2.me/theorems/4c87e953-828c-4561-b7ef-901894e2a2e8
-- title:
--   Eq. (23): the 1D Kirchhoff integral is $k_0$ times a Fourier transform over the lag
-- statement:
--   Let $k_0>0$ be the water wavenumber and $h>0$ the rms height of a rough interface. Let $C:\mathbb{R}\to\mathbb{R}$ be its normalized correlation function, so $C(0)=1$, $C(-x)=C(x)$ and $|C|\le1$. Let $\Delta K_x\in\mathbb{R}$ and $\eta\in\mathbb{C}$, and assume that $x\mapsto e^{\eta^2h^2C(x)}-1$ is integrable on $\mathbb{R}$. Then the one-dimensional Kirchhoff integral of eq. (23),
--
--   $$I^{1D}(\eta)=2e^{-\eta^2h^2}\int_0^\infty\cos\Big(\frac{\Delta K_x u}{k_0}\Big)\Big[e^{\eta^2h^2C(u/k_0)}-1\Big]\,du,$$
--
--   equals $k_0$ times the Fourier transform over the horizontal lag $x$:
--
--   $$I^{1D}(\eta)=k_0\int_{-\infty}^{\infty}e^{-i\Delta K_x x}\,e^{-\eta^2h^2}\Big[e^{\eta^2h^2C(x)}-1\Big]\,dx .$$
--
--   For Gaussian roughness the right-hand side is the incoherent part of $\langle e^{-i\eta(f(x)-f(0))}\rangle$ integrated against $e^{-i\Delta K_x x}$.
--
--   **Formalization Note** The paper gives eq. (23) only as a definition, without a derivation, and does not define $\eta$. The paper does not state this Fourier-transform identity. Following claim c002, the statement records it as an elementary reformulation of eq. (23) (change of variables $u=k_0x$ and evenness of $C$). It is not a claim of the paper. $\eta$ is allowed to be complex, which covers real $\eta$. Integrability, which the paper assumes implicitly, makes the integral in eq. (23) absolutely convergent. Evenness of $C$ follows from stationarity, eq. (8).
-- source:
--   Olson and Jackson, Scattering from layered seafloors: Comparisons between theory and integral equations, arXiv:2009.12420v1 (2020), claim c002; Section III, eq. (23), with eqs. (8)-(9), PDF p. 4

import Mathlib
import Definitions.Def_Arxiv2009_12420_Basic

open Complex MeasureTheory

namespace Arxiv2009_12420

theorem kirchhoff_integral_1d_fourier_form (k0 h dKx : ℝ) (hk0 : 0 < k0) (hh : 0 < h)
    (C : ℝ → ℝ) (hC : IsNormalizedCorrelation C) (η : ℂ)
    (hint : Integrable (fun x : ℝ => cexp (η ^ 2 * (h : ℂ) ^ 2 * (C x : ℂ)) - 1)) :
    kirchhoffIntegral1D k0 h dKx C η =
      (k0 : ℂ) * ∫ x : ℝ, cexp (-(I * (dKx : ℂ) * (x : ℂ))) *
        (cexp (-(η ^ 2 * (h : ℂ) ^ 2)) * (cexp (η ^ 2 * (h : ℂ) ^ 2 * (C x : ℂ)) - 1)) := by sorry

end Arxiv2009_12420
