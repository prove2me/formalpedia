-- Prove2me | Theorems.Thm_DeepLearningTheory_gaussian_generating_function
-- name    : DeepLearningTheory.gaussian_generating_function
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T21:17:19.777984+00:00
-- url     : https://prove2.me/theorems/c3c6dcb2-1ee0-4e43-a166-9d8a5f9c5c5d
-- title:
--   Gaussian generating function $Z_{K,J}$ (eq. 1.41)
-- statement:
--   Let $K$ be a symmetric positive-definite real $N\times N$ matrix, with inverse $K^{\mu\nu}$, and let $J\in\mathbb{R}^N$ be a source. Then the generating function (1.38) has the closed form
--
--   $$Z_{K,J} = \int_{\mathbb{R}^N}\exp\Big(-\tfrac12\sum_{\mu,\nu} z_\mu K^{\mu\nu} z_\nu + \sum_\mu J^\mu z_\mu\Big)d^N z = \sqrt{|2\pi K|}\;\exp\Big(\tfrac12\sum_{\mu,\nu} J^\mu K_{\mu\nu} J^\nu\Big).$$
--
--   Its Taylor coefficients at $J=0$ are the Gaussian moments, which is how the book derives Wick's theorem.
-- source:
--   Daniel A. Roberts and Sho Yaida (with Boris Hanin), *The Principles of Deep Learning Theory*, arXiv:2106.10165v2, https://arxiv.org/abs/2106.10165, §1.1, pp. 20–21, eqs. (1.38), (1.41) (page numbers are the book's printed page numbers)

import Mathlib
import Definitions.Def_DLT_GaussianIntegrals

open MeasureTheory

namespace DeepLearningTheory

theorem gaussian_generating_function {N : ℕ} (K : Matrix (Fin N) (Fin N) ℝ)
    (hK : K.PosDef) (J : Fin N → ℝ) :
    ∫ z : Fin N → ℝ, Real.exp (-(1 / 2) * gaussQuadForm K z + ∑ μ : Fin N, J μ * z μ)
      = Real.sqrt ((2 * Real.pi) ^ N * K.det) *
          Real.exp ((1 / 2) * ∑ μ : Fin N, ∑ ν : Fin N, J μ * K μ ν * J ν) := by sorry

end DeepLearningTheory
