-- Prove2me | Theorems.Thm_DuanCV_Gauss_gaussian_quadrature_variance
-- name    : DuanCV.Gauss.gaussian_quadrature_variance
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:57:36.529792+00:00
-- url     : https://prove2.me/theorems/85b2868d-043a-4b07-9837-7a70cac946e7
-- title:
--   The variance of a quadrature in a Gaussian state is $\tfrac12 w^TVw$
-- statement:
--   Let $\rho$ be a two-mode Gaussian state with covariance matrix $V$ and arbitrary first moments, and let $w\in\mathbb R^4$. Then
--
--   $$\bigl\langle(\Delta(w\cdot\hat r))^2\bigr\rangle_\rho=\frac12\,w^TVw .$$
--
--   This is the computation that turns the operator inequality (3) into the parameter inequality (16). In these conventions the vacuum has $V=I$, so each quadrature of the vacuum has variance $\tfrac12$.
--
--   Differences from the source:
--   - encoding: the correlation matrix M of Eq. (6), with linear terms removed by local displacements → the covariance V of GaussianWithCovariance: density operator, V ≻ 0, V + iJ ⪰ 0, finite mean energy, arbitrary first moments, and convergent Weyl traces equal to exp(−¼vᵀVv + i mᵀv); reason: v = √2 λ in Eqs. (5)–(6) gives M = V (vacuum V = I); the extra conditions hold for every Gaussian state, and first moments are kept rather than displaced away
--   - encoding: ⟨(Δû)²⟩_ρ for a quadrature û = w·r̂ → the variance in ℝ≥0∞ of the unique probability law on ℝ whose characteristic function is the Weyl trace tr ρ exp(i t w·r̂); reason: this is the variance of the observable; the value is ⊤ when the second moment is infinite, a case the paper does not discuss and in which (3) holds trivially
-- source:
--   Duan, Giedke, Cirac, Zoller, Inseparability criterion for continuous variable systems, arXiv:quant-ph/9908056v2, p. 4, before Eq. (16), with Eqs. (5)–(6), p. 2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P47
import Definitions.Def_DuanCV_Gauss_quadVariance

open QAlgorithms.Papers.Independent.Frontier30.P08 (QuadratureIndex)
open QAlgorithms.Papers.Independent.Gap48.P47 (TwoModeGaussianDensity)

namespace DuanCV.Gauss

/-- **The variance of a quadrature in a Gaussian state is `½ wᵀVw`.**
Duan, Giedke, Cirac, Zoller, *Inseparability criterion for continuous variable systems*, arXiv:quant-ph/9908056v2, p. 4 (the step "calculating ⟨(Δû)²⟩ + ⟨(Δv̂)²⟩ using the correlation matrix", before Eq. (16)),
with the conventions of Eqs. (5)–(6), p. 2.

**Formalization Note.** From (5)–(6), `exp(-½λMλᵀ) = exp(-¼vᵀMv)` at `v = √2 λ`, so the paper's `M` is
the covariance `V` of `GaussianWithCovariance`, with vacuum `V = I`. The factor `½` gives vacuum
variance `½`, the textbook value for `[x̂, p̂] = i`. First moments are arbitrary. -/
theorem gaussian_quadrature_variance (ρ : TwoModeGaussianDensity) (w : QuadratureIndex 2 → ℝ) :
    quadVariance ρ.density.coefficients w =
      ENNReal.ofReal ((∑ i, ∑ j, w i * ρ.covariance i j * w j) / 2) := by sorry

end DuanCV.Gauss
