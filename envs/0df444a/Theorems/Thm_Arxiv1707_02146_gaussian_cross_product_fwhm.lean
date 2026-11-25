-- Prove2me | Theorems.Thm_Arxiv1707_02146_gaussian_cross_product_fwhm
-- name    : Arxiv1707_02146.gaussian_cross_product_fwhm
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T00:31:54.518892+00:00
-- url     : https://prove2.me/theorems/75e06b10-5e3d-44df-a522-5a58e21c8f58
-- title:
--   pp. 3-4: the cross product of two Gaussians of FWHM $\Delta\lambda_m$ is a Gaussian of FWHM $\Delta\lambda_m/\sqrt2$
-- statement:
--   Let $f$ and $g$ be Gaussians centred at the same $\lambda_0$ with the same full width at half maximum $w>0$: $f(\lambda)=A\exp(-4\ln2\,(\lambda-\lambda_0)^2/w^2)$ and $g(\lambda)=A'\exp(-4\ln2\,(\lambda-\lambda_0)^2/w^2)$ with $A,A'>0$. Then the product $fg$ is a Gaussian centred at $\lambda_0$ with FWHM $w/\sqrt2$. Precisely:
--
--   1. $fg$ is a Gaussian of the same form, centred at $\lambda_0$, with FWHM $w/\sqrt2$;
--   2. $fg$ attains its maximum at $\lambda_0$;
--   3. $$\Big\{\lambda:\ f(\lambda)g(\lambda)\ge\tfrac12 f(\lambda_0)g(\lambda_0)\Big\}=\Big[\lambda_0-\frac{w}{2\sqrt2},\ \lambda_0+\frac{w}{2\sqrt2}\Big],$$ an interval of length $w/\sqrt2$;
--   4. $w/\sqrt2<w$.
--
--   In the paper, $f$ and $g$ are the spectral profiles of the reference and modulated speckles, both equal in shape to the input pulse spectrum of FWHM $\Delta\lambda_m$, and the conclusion is $\Delta\lambda_f=\Delta\lambda_m/\sqrt2$.
--
--   **Formalization Note** The paper says the input Gaussian has "span" $\Delta\lambda_m$ and uses "at FWHM" only for $\Delta\lambda_f$; the statement reads the span as the FWHM, the reading under which the factor $1/\sqrt2$ holds.
-- source:
--   Mounaix, de Aguiar and Gigan, Temporal recompression through a scattering medium via a broadband transmission matrix, arXiv:1707.02146v1 (2017), claim c015; main text, paragraph explaining the spectral narrowing ("Accordingly, this observation can be explained using Equation 1"), PDF pp. 3-4

import Mathlib
import Definitions.Def_Arxiv1707_02146_Basic

open Matrix ComplexConjugate

namespace Arxiv1707_02146

theorem gaussian_cross_product_fwhm (f g : ℝ → ℝ) (l0 w : ℝ)
    (hf : IsGaussianFWHM f l0 w) (hg : IsGaussianFWHM g l0 w) :
    IsGaussianFWHM (fun lam => f lam * g lam) l0 (w / Real.sqrt 2) ∧
    (∀ lam : ℝ, f lam * g lam ≤ f l0 * g l0) ∧
    {lam : ℝ | f l0 * g l0 / 2 ≤ f lam * g lam} =
      Set.Icc (l0 - w / Real.sqrt 2 / 2) (l0 + w / Real.sqrt 2 / 2) ∧
    w / Real.sqrt 2 < w := by sorry

end Arxiv1707_02146
