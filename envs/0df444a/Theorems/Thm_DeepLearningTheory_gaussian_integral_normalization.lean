-- Prove2me | Theorems.Thm_DeepLearningTheory_gaussian_integral_normalization
-- name    : DeepLearningTheory.gaussian_integral_normalization
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T21:16:01.754998+00:00
-- url     : https://prove2.me/theorems/a67e67bd-50d0-487c-ae1b-e1b15e502b62
-- title:
--   Gaussian normalization $I_K=\sqrt{|2\pi K|}$ (eq. 1.30)
-- statement:
--   Let $K$ be a symmetric positive-definite real $N\times N$ matrix. Then
--
--   $$\int_{\mathbb{R}^N} \exp\Big(-\tfrac12\sum_{\mu,\nu=1}^N z_\mu (K^{-1})_{\mu\nu} z_\nu\Big)\,d^N z = \sqrt{|2\pi K|} = \sqrt{(2\pi)^N\det K}.$$
--
--   This fixes the normalization of the multivariable Gaussian distribution (1.31), so that its density integrates to one.
-- source:
--   Daniel A. Roberts and Sho Yaida (with Boris Hanin), *The Principles of Deep Learning Theory*, arXiv:2106.10165v2, https://arxiv.org/abs/2106.10165, §1.1, p. 19, eq. (1.30) (page numbers are the book's printed page numbers)

import Mathlib
import Definitions.Def_DLT_GaussianIntegrals

open MeasureTheory

namespace DeepLearningTheory

theorem gaussian_integral_normalization {N : ℕ} (K : Matrix (Fin N) (Fin N) ℝ)
    (hK : K.PosDef) :
    ∫ z : Fin N → ℝ, Real.exp (-(1 / 2) * gaussQuadForm K z)
      = Real.sqrt ((2 * Real.pi) ^ N * K.det) := by sorry

end DeepLearningTheory
