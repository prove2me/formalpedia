-- Prove2me | Theorems.Thm_DeepLearningTheory_gaussian_four_point
-- name    : DeepLearningTheory.gaussian_four_point
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T21:34:47.326573+00:00
-- url     : https://prove2.me/theorems/e9437fad-cd5d-4095-b537-ed3bc75cc877
-- title:
--   Gaussian four-point function (eq. 1.44)
-- statement:
--   Let $K$ be a symmetric positive-definite real $N\times N$ matrix and let $z$ follow the zero-mean Gaussian distribution with covariance $K$. For all indices $\mu_1,\dots,\mu_4$,
--
--   $$\mathbb{E}[z_{\mu_1}z_{\mu_2}z_{\mu_3}z_{\mu_4}] = K_{\mu_1\mu_2}K_{\mu_3\mu_4}+K_{\mu_1\mu_3}K_{\mu_2\mu_4}+K_{\mu_1\mu_4}K_{\mu_2\mu_3}.$$
--
--   This is the $2m=4$ case of Wick's theorem, with three pairings.
-- source:
--   Daniel A. Roberts and Sho Yaida (with Boris Hanin), *The Principles of Deep Learning Theory*, arXiv:2106.10165v2, https://arxiv.org/abs/2106.10165, §1.1, p. 22, eq. (1.44) (page numbers are the book's printed page numbers)

import Mathlib
import Definitions.Def_DLT_GaussianIntegrals

open MeasureTheory

namespace DeepLearningTheory

theorem gaussian_four_point {N : ℕ} (K : Matrix (Fin N) (Fin N) ℝ) (hK : K.PosDef)
    (μ₁ μ₂ μ₃ μ₄ : Fin N) :
    gaussExpect K (fun z => z μ₁ * z μ₂ * z μ₃ * z μ₄)
      = K μ₁ μ₂ * K μ₃ μ₄ + K μ₁ μ₃ * K μ₂ μ₄ + K μ₁ μ₄ * K μ₂ μ₃ := by sorry

end DeepLearningTheory
