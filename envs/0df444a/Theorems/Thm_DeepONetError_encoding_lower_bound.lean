-- Prove2me | Theorems.Thm_DeepONetError_encoding_lower_bound
-- name    : DeepONetError.encoding_lower_bound
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T05:29:39.415805+00:00
-- url     : https://prove2.me/theorems/576e2d18-62c2-4d1e-a197-4050847e7194
-- title:
--   Theorem 3.8: lower bound on the encoding error for linear decoders
-- statement:
--   Let $D\subset\mathbb{R}^d$ and let $\mu$ be a Borel probability measure on $X=L^2(D)$ with $\int_X\|u\|^2_{L^2}\,d\mu<\infty$ and $\int_Xu\,d\mu(u)=0$. Let $\lambda_1\ge\lambda_2\ge\cdots$ be the eigenvalues, repeated according to multiplicity, of the covariance operator $\Gamma_\mu$. For any encoder $\mathcal{E}:X\to\mathbb{R}^m$ and any linear decoder $\mathcal{D}:\mathbb{R}^m\to X$,
--
--   $$\int_X\|\mathcal{D}\circ\mathcal{E}(u)-u\|^2_{L^2}\,d\mu(u)\ge\sum_{k>m}\lambda_k,\qquad\text{hence}\qquad\widehat{\mathcal{E}}_{\mathcal{E}}\ge\sqrt{\sum_{k>m}\lambda_k}.$$
--
--   With a linear decoder, no encoder using $m$ numbers can beat the tail of the spectrum of the input covariance.
--
--   **Formalization Note** The eigenvalues are given by a spectral decomposition of $\Gamma_\mu$, indexed from $0$. The integral is a lower Lebesgue integral in $[0,\infty]$, so no measurability of $\mathcal{E}$ is needed.
-- source:
--   Lanthaler, Mishra and Karniadakis, Error estimates for DeepOnets: A deep learning framework in infinite dimensions, arXiv:2102.09618v3 (2022), Section 3.2.3, Theorem 3.8, eq. (3.12), p. 14; proof in Appendix C.10, p. 91

import Mathlib
import Definitions.Def_DeepONetError_Basic

open MeasureTheory

namespace DeepONetError

theorem encoding_lower_bound {d m : ℕ} {Dset : Set (Fin d → ℝ)}
    [MeasurableSpace (L2 Dset)] [BorelSpace (L2 Dset)]
    (mu : Measure (L2 Dset)) (hmu : IsP2 mu) (hmean : mean mu = 0)
    (lam : ℕ → ℝ) (phi : ℕ → L2 Dset) (hspec : IsSpectralDecomp (covOp mu) lam phi)
    (E : L2 Dset → EuclideanSpace ℝ (Fin m)) (Dec : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] L2 Dset) :
    (∑' k, ENNReal.ofReal (lam (k + m))) ≤ (∫⁻ u, ‖Dec (E u) - u‖ₑ ^ 2 ∂mu) ∧
      (∑' k, ENNReal.ofReal (lam (k + m))) ^ ((1 : ℝ) / 2) ≤ encErr mu E Dec := by sorry

end DeepONetError
