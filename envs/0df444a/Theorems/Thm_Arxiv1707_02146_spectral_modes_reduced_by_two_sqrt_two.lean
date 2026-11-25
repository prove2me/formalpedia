-- Prove2me | Theorems.Thm_Arxiv1707_02146_spectral_modes_reduced_by_two_sqrt_two
-- name    : Arxiv1707_02146.spectral_modes_reduced_by_two_sqrt_two
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T00:35:29.067953+00:00
-- url     : https://prove2.me/theorems/7ff55d90-6fba-489f-8dad-c2883f719443
-- title:
--   Conclusion: focusing with the BBTM reduces $N_\lambda$ by a factor $2\sqrt2$
-- statement:
--   Let $\kappa>0$ and let the medium and the focus have spectral correlation bandwidths $\delta\lambda_m,\delta\lambda_f>0$ and traversal times $\tau_m=\kappa/\delta\lambda_m$, $\tau_f=\kappa/\delta\lambda_f$, with the measured ratio $\tau_f/\tau_m=1/2$. Let the reference and modulated speckle spectra be Gaussians $f,g$ centred at $\lambda_0$ with FWHM $\Delta\lambda_m$, and let the focus envelope $fg$ be a Gaussian centred at $\lambda_0$ with FWHM $\Delta\lambda_f$. Then
--   $$\delta\lambda_f=2\,\delta\lambda_m,\qquad\Delta\lambda_f=\frac{\Delta\lambda_m}{\sqrt2},\qquad N_{\lambda}=\frac{\Delta\lambda_m}{\delta\lambda_m}=2\sqrt2\,\frac{\Delta\lambda_f}{\delta\lambda_f}=2\sqrt2\,N_{\lambda,f}.$$
--   Here $\Delta\lambda_m$ is the spectral width of the speckle behind the medium, which the paper takes equal to the input pulse width $\Delta\lambda$, so $N_\lambda$ is the paper's $\Delta\lambda/\delta\lambda_m$.
--
--   That is, with a Gaussian input pulse, focusing with the BBTM reduces the number of spectral degrees of freedom by the factor $2\sqrt2\approx2.83$: a factor $2$ from the increase of the spectral correlation bandwidth and a factor $\sqrt2$ from the narrowing of the spectral envelope.
--
--   **Formalization Note** The paper writes "a factor $\sim2\sqrt2$"; the model gives exactly $2\sqrt2$, which is stated. The ratio $\tau_f/\tau_m=0.5$ is the paper's measurement and enters as a hypothesis. The relation $\tau=\kappa/\delta\lambda$ is applied to the focus with the same constant as for the medium, as in the preceding statement.
-- source:
--   Mounaix, de Aguiar and Gigan, Temporal recompression through a scattering medium via a broadband transmission matrix, arXiv:1707.02146v1 (2017), claim c016; Conclusion paragraph, PDF p. 4, combining tau_f/tau_m = 0.5 (p. 3), tau_m proportional to 1/delta_lambda_m and N_lambda = Delta_lambda/delta_lambda_m (p. 2) and the Gaussian cross product (pp. 3-4)

import Mathlib
import Definitions.Def_Arxiv1707_02146_Basic

open Matrix ComplexConjugate

namespace Arxiv1707_02146

theorem spectral_modes_reduced_by_two_sqrt_two (κ bwm bwf wm wf l0 : ℝ) (f g : ℝ → ℝ)
    (hκ : 0 < κ) (hbwm : 0 < bwm) (hbwf : 0 < bwf)
    (hratio : traversalTime κ bwf / traversalTime κ bwm = 1 / 2)
    (hf : IsGaussianFWHM f l0 wm) (hg : IsGaussianFWHM g l0 wm)
    (hfocus : IsGaussianFWHM (fun lam => f lam * g lam) l0 wf) :
    bwf = 2 * bwm ∧ wf = wm / Real.sqrt 2 ∧
    numSpectralModes wm bwm = 2 * Real.sqrt 2 * numSpectralModes wf bwf := by sorry

end Arxiv1707_02146
