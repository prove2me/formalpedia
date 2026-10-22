-- Prove2me | Theorems.Thm_FermiCap_Gaussian_eq_22
-- name    : FermiCap.Gaussian.eq_22
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:42:49.247992+00:00
-- url     : https://prove2.me/theorems/cbcce592-a816-48ba-8779-c1272b0a8bb3
-- title:
--   Equation (22) — channel action on even Gaussian covariances
-- statement:
--   Let $\rho$ be an even Gaussian input state and $b_p\in[0,1]$ the attenuation coefficients of $\Phi_b$. The output remains even Gaussian. If $M(\rho)$ is its input covariance matrix and $B=\operatorname{diag}(b_1,\ldots,b_{2n})$, then
--   $$M(\Phi_b(\rho))=B M(\rho) B^{\mathsf T}.$$
--   This connects the channel's Majorana action to the covariance description of even Gaussian states.
-- source:
--   Bravyi, Classical capacity of fermionic product channels, arXiv:quant-ph/0507282v1, p. 5, §III.D, eq. (22)

import Mathlib
import Definitions.Def_FermiCap_Gaussian_Capacity

noncomputable section
open Matrix

namespace FermiCap.Gaussian

/-- Eq. (22) and §III.D: Gaussianity and covariance under the channel. -/
theorem eq_22 (n : ℕ) (b : Fin (2 * n) → ℝ) (ρ : Op n)
    (hb : ∀ p, 0 ≤ b p ∧ b p ≤ 1) (hρ : IsEvenGaussian ρ) :
    IsEvenGaussian (channel n b ρ) ∧
      covariance (channel n b ρ) =
        attenuationDiagonal n b * covariance ρ * (attenuationDiagonal n b)ᵀ := by sorry

end FermiCap.Gaussian
