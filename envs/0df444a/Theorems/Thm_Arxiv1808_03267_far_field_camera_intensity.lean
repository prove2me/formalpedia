-- Prove2me | Theorems.Thm_Arxiv1808_03267_far_field_camera_intensity
-- name    : Arxiv1808_03267.far_field_camera_intensity
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T05:12:26.484689+00:00
-- url     : https://prove2.me/theorems/3fbd6ae7-37b8-5e07-a3cf-42c891618fd9
-- title:
--   Eq. (1): in the far field the camera image is the power spectrum of the object field
-- statement:
--   Let $\lambda>0$, let $E_{object}=E_{illum}T$ be integrable on $\mathbb{R}^2$, and let $\varphi:\mathbb{R}^2\to\mathbb{R}$ be any realization of the phase of a thin second layer. Let $E(x',L)$ be the field at distance $L$ (Fresnel integral) and $I_{camera}(x')=|e^{i\varphi(x')}E(x',L)|^2$. Then for every $u\in\mathbb{R}^2$:
--
--   1. (far field: the field is the Fourier transform of the object field) as $L\to\infty$,
--   $$i\lambda L\,e^{-ikL}\,e^{-i\pi\lambda L|u|^2}\,E(\lambda L\,u,\,L)\;\longrightarrow\;\mathcal{F}(E_{object})(u);$$
--   2. (thin phase mask leaves the intensity unchanged) $I_{camera}(x')=|E(x',L)|^2$ for every $L$ and $x'$;
--   3. (eq. 1: the camera image is the power spectrum) as $L\to\infty$,
--   $$(\lambda L)^2\,I_{camera}(\lambda L\,u)\;\longrightarrow\;\big|\mathcal{F}(E_{object})(u)\big|^2.$$
--
--   **Formalization Note** The paper writes $E(x',y',L)\propto\mathcal{F}(E_{object})$ and $I_{camera}\propto|\mathcal{F}(E_{object})|^2$ "if $L$ is larger than the far-field distance". Here the far-field condition is the limit $L\to\infty$, the camera point is $x'=\lambda L\,u$ (the coordinate scaling the paper leaves implicit), and the proportionality constants are written out. The field is proportional to $\mathcal{F}(E_{object})(x'/\lambda L)$ only up to the position-dependent phase $e^{ikL}e^{i\pi|x'|^2/(\lambda L)}/(i\lambda L)$, which part 1 removes explicitly; this phase does not affect the intensity. The propagation law is the Fresnel integral (see the definitions). Integrability of $E_{object}$ is assumed so that the diffraction and Fourier integrals exist; it holds for the paper's bounded object of finite size.
-- source:
--   Stern and Katz, Non-invasive Focusing Through Scattering Layers Using Speckle-Correlations, arXiv:1808.03267v1 (2018), claim c001; main text (unsectioned), eq. (1) and the paragraph before and after it, PDF pp. 1-2

import Mathlib
import Definitions.Def_Arxiv1808_03267_Basic

open MeasureTheory Filter Topology
open scoped FourierTransform

namespace Arxiv1808_03267

theorem far_field_camera_intensity (lam : ℝ) (hlam : 0 < lam) (Eillum T : Plane → ℂ)
    (hE : Integrable (objectField Eillum T)) (φ : Plane → ℝ) (u : Plane) :
    Tendsto (fun L : ℝ => Complex.I * ((lam * L : ℝ) : ℂ) *
        Complex.exp (-(((2 * Real.pi * L / lam : ℝ) : ℂ) * Complex.I)) *
        Complex.exp (-(((Real.pi * lam * L * ‖u‖ ^ 2 : ℝ) : ℂ) * Complex.I)) *
        fresnelField lam L (objectField Eillum T) ((lam * L) • u))
      atTop (𝓝 (𝓕 (objectField Eillum T) u)) ∧
    (∀ (L : ℝ) (x' : Plane), cameraIntensity lam L φ (objectField Eillum T) x' =
        ‖fresnelField lam L (objectField Eillum T) x'‖ ^ 2) ∧
    Tendsto (fun L : ℝ => (lam * L) ^ 2 *
        cameraIntensity lam L φ (objectField Eillum T) ((lam * L) • u))
      atTop (𝓝 (powerSpectrum (objectField Eillum T) u)) := by sorry

end Arxiv1808_03267
