-- Prove2me | Theorems.Thm_Arxiv1808_03267_camera_image_fourier_transform_autocorrelation
-- name    : Arxiv1808_03267.camera_image_fourier_transform_autocorrelation
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T05:13:36.122411+00:00
-- url     : https://prove2.me/theorems/8fe5dee9-0f66-49e2-9b90-e096b5324696
-- title:
--   Eq. (2): the Fourier transform of the far-field camera image is the object-field autocorrelation
-- statement:
--   Let $\lambda>0$, let $E_{object}=E_{illum}T\in L^1(\mathbb{R}^2)\cap L^2(\mathbb{R}^2)$, let $\varphi:\mathbb{R}^2\to\mathbb{R}$ be any realization of the phase of a thin second layer, and let $I_{camera}^{(L)}(x')=|e^{i\varphi(x')}E(x',L)|^2$ be the camera image when the second layer is at distance $L$ from the object. Then for every $x\in\mathbb{R}^2$,
--   $$\mathcal{F}^{-1}\big(I_{camera}^{(L)}\big)\Big(\frac{x}{\lambda L}\Big)=\int_{\mathbb{R}^2}I_{camera}^{(L)}(x')\,e^{2\pi i\langle x',x\rangle/(\lambda L)}\,dx'\;\longrightarrow\;A(x)=\int_{\mathbb{R}^2}\overline{E_{object}(y)}\,E_{object}(x+y)\,dy\qquad(L\to\infty).$$
--   That is, in the far field the Fourier transform of a single camera image gives the autocorrelation of the field just after the object.
--
--   **Formalization Note** The paper's eq. (2), $\tilde F(I_{camera}(x'',y''))\propto E_{object}\star E_{object}=A(x,y)$, holds under the far-field assumption of eq. (1); here that assumption is the limit $L\to\infty$. The paper's undefined transform variable $(x'',y'')$ is made explicit: the transform of the camera image is evaluated at the frequency $x/(\lambda L)$, which is the scaling between camera coordinates and spatial frequency. With this scaling the constant of proportionality is $1$. The transform is the inverse Fourier transform; the forward transform gives $A(-x)=\overline{A(x)}$. The hypothesis $E_{object}\in L^1\cap L^2$ is the integrability needed for every integral to exist; it holds for the paper's bounded object of finite size.
-- source:
--   Stern and Katz, Non-invasive Focusing Through Scattering Layers Using Speckle-Correlations, arXiv:1808.03267v1 (2018), claim c002; main text (unsectioned), eqs. (1)-(2) and the paragraph after eq. (2), PDF p. 2

import Mathlib
import Definitions.Def_Arxiv1808_03267_Basic

open MeasureTheory Filter Topology
open scoped FourierTransform

namespace Arxiv1808_03267

theorem camera_image_fourier_transform_autocorrelation (lam : ℝ) (hlam : 0 < lam)
    (Eillum T : Plane → ℂ) (hE1 : Integrable (objectField Eillum T))
    (hE2 : MemLp (objectField Eillum T) 2) (φ : Plane → ℝ) (x : Plane) :
    Tendsto (fun L : ℝ => 𝓕⁻ (fun x' : Plane =>
        (cameraIntensity lam L φ (objectField Eillum T) x' : ℂ)) ((lam * L)⁻¹ • x))
      atTop (𝓝 (autocorrelation (objectField Eillum T) x)) := by sorry

end Arxiv1808_03267
