-- Prove2me | Theorems.Thm_Arxiv1808_03267_wiener_khinchin_power_spectrum
-- name    : Arxiv1808_03267.wiener_khinchin_power_spectrum
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T05:12:56.879378+00:00
-- url     : https://prove2.me/theorems/fb214cc2-ef1e-5e1a-a104-1c5f025137ef
-- title:
--   Eq. (2), Wiener-Khinchin step: the Fourier transform of the power spectrum is the field autocorrelation
-- statement:
--   (Wiener-Khinchin theorem.) Let $E:\mathbb{R}^2\to\mathbb{C}$ be in $L^1(\mathbb{R}^2)\cap L^2(\mathbb{R}^2)$. Then for every $x\in\mathbb{R}^2$,
--   $$\mathcal{F}^{-1}\big(|\mathcal{F}(E)|^2\big)(x)=\int_{\mathbb{R}^2}|\mathcal{F}(E)(u)|^2e^{2\pi i\langle u,x\rangle}\,du=\int_{\mathbb{R}^2}\overline{E(y)}\,E(x+y)\,dy=(E\star E)(x).$$
--
--   **Formalization Note** The paper invokes this theorem without stating hypotheses and writes the transform as $\tilde F$ with "$\propto$". Here the transform is the inverse Fourier transform, for which the identity holds with constant $1$; the forward transform gives $(E\star E)(-x)=\overline{(E\star E)(x)}$. The hypothesis $E\in L^1\cap L^2$ makes $\mathcal{F}(E)$ a convergent integral, $|\mathcal{F}(E)|^2$ integrable and $E\star E$ finite; it holds for the paper's bounded object of finite size.
-- source:
--   Stern and Katz, Non-invasive Focusing Through Scattering Layers Using Speckle-Correlations, arXiv:1808.03267v1 (2018), claim c002; main text (unsectioned), sentence introducing eq. (2) and eq. (2), PDF p. 2

import Mathlib
import Definitions.Def_Arxiv1808_03267_Basic

open MeasureTheory Filter Topology
open scoped FourierTransform

namespace Arxiv1808_03267

theorem wiener_khinchin_power_spectrum (E : Plane → ℂ) (hE1 : Integrable E) (hE2 : MemLp E 2)
    (x : Plane) :
    𝓕⁻ (fun u : Plane => (powerSpectrum E u : ℂ)) x = autocorrelation E x := by sorry

end Arxiv1808_03267
