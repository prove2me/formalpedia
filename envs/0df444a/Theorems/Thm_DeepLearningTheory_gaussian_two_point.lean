-- Prove2me | Theorems.Thm_DeepLearningTheory_gaussian_two_point
-- name    : DeepLearningTheory.gaussian_two_point
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T21:32:57.210188+00:00
-- url     : https://prove2.me/theorems/5565111d-2edf-4bb8-94c0-7edffe218bff
-- title:
--   Gaussian two-point function $\mathbb{E}[z_{\mu_1}z_{\mu_2}]=K_{\mu_1\mu_2}$ (eq. 1.43)
-- statement:
--   Let $K$ be a symmetric positive-definite real $N\times N$ matrix and let $z$ follow the zero-mean Gaussian distribution with covariance $K$ (density (1.31)). For all $\mu_1,\mu_2$,
--
--   $$\mathbb{E}[z_{\mu_1}z_{\mu_2}] = K_{\mu_1\mu_2}.$$
--
--   This justifies calling $K$ the covariance.
-- source:
--   Daniel A. Roberts and Sho Yaida (with Boris Hanin), *The Principles of Deep Learning Theory*, arXiv:2106.10165v2, https://arxiv.org/abs/2106.10165, §1.1, p. 22, eq. (1.43) (page numbers are the book's printed page numbers)

import Mathlib
import Definitions.Def_DLT_GaussianIntegrals

open MeasureTheory

namespace DeepLearningTheory

theorem gaussian_two_point {N : ℕ} (K : Matrix (Fin N) (Fin N) ℝ) (hK : K.PosDef)
    (μ₁ μ₂ : Fin N) :
    gaussExpect K (fun z => z μ₁ * z μ₂) = K μ₁ μ₂ := by sorry

end DeepLearningTheory
