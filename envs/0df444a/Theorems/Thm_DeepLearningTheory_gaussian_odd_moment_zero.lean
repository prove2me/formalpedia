-- Prove2me | Theorems.Thm_DeepLearningTheory_gaussian_odd_moment_zero
-- name    : DeepLearningTheory.gaussian_odd_moment_zero
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T21:27:32.523986+00:00
-- url     : https://prove2.me/theorems/e440b47d-62a7-4362-8d63-0f1ede199bad
-- title:
--   Odd Gaussian moments vanish
-- statement:
--   Let $K$ be a symmetric positive-definite real $N\times N$ matrix and let $z$ follow the zero-mean Gaussian distribution with covariance $K$. For every $m\ge0$ and all indices $\mu_1,\dots,\mu_{2m+1}\in\{1,\dots,N\}$,
--
--   $$\mathbb{E}\big[z_{\mu_1}z_{\mu_2}\cdots z_{\mu_{2m+1}}\big] = 0.$$
--
--   Together with Wick's theorem this determines all moments of the Gaussian.
-- source:
--   Daniel A. Roberts and Sho Yaida (with Boris Hanin), *The Principles of Deep Learning Theory*, arXiv:2106.10165v2, https://arxiv.org/abs/2106.10165, §1.1, p. 22, discussion following eq. (1.42) (page numbers are the book's printed page numbers)

import Mathlib
import Definitions.Def_DLT_GaussianIntegrals

open MeasureTheory

namespace DeepLearningTheory

theorem gaussian_odd_moment_zero {N : ℕ} (K : Matrix (Fin N) (Fin N) ℝ) (hK : K.PosDef)
    (m : ℕ) (μs : Fin (2 * m + 1) → Fin N) :
    gaussExpect K (fun z => ∏ a : Fin (2 * m + 1), z (μs a)) = 0 := by sorry

end DeepLearningTheory
