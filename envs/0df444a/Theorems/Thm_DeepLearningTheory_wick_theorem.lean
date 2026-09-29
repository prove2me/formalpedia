-- Prove2me | Theorems.Thm_DeepLearningTheory_wick_theorem
-- name    : DeepLearningTheory.wick_theorem
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T21:42:34.884982+00:00
-- url     : https://prove2.me/theorems/a9908763-45f8-4148-814f-79ad6c1c44b0
-- title:
--   Wick's theorem for the multivariable Gaussian (eq. 1.45)
-- statement:
--   **Wick's theorem.** Let $K$ be a symmetric positive-definite real $N\times N$ matrix and let $z$ follow the zero-mean Gaussian distribution with covariance $K$ (density (1.31)). For every $m\ge0$ and all indices $\mu_1,\dots,\mu_{2m}\in\{1,\dots,N\}$ (repetitions allowed),
--
--   $$\mathbb{E}[z_{\mu_1}\cdots z_{\mu_{2m}}] = \sum_{\text{all pairings}} K_{\mu_{k_1}\mu_{k_2}}\cdots K_{\mu_{k_{2m-1}}\mu_{k_{2m}}},$$
--
--   where the sum runs over the $(2m-1)!!$ distinct ways of pairing the labels $1,\dots,2m$, and each pair $\{k,k'\}$ contributes one factor $K_{\mu_k\mu_{k'}}$ (a Wick contraction).
--
--   This formula evaluates every Gaussian moment and underlies all correlator computations in the book.
--
--   **Formalization Note** A pairing is encoded as a fixed-point-free involution $\sigma$ of $\{0,\dots,2m-1\}$; the product runs over labels $a$ with $a<\sigma(a)$, so each pair appears exactly once.
-- source:
--   Daniel A. Roberts and Sho Yaida (with Boris Hanin), *The Principles of Deep Learning Theory*, arXiv:2106.10165v2, https://arxiv.org/abs/2106.10165, §1.1, pp. 22–23, eq. (1.45) (page numbers are the book's printed page numbers)

import Mathlib
import Definitions.Def_DLT_GaussianIntegrals

open MeasureTheory

namespace DeepLearningTheory

theorem wick_theorem {N : ℕ} (K : Matrix (Fin N) (Fin N) ℝ) (hK : K.PosDef)
    (m : ℕ) (μs : Fin (2 * m) → Fin N) :
    gaussExpect K (fun z => ∏ a : Fin (2 * m), z (μs a))
      = ∑ σ ∈ pairings (2 * m),
          ∏ a ∈ Finset.univ.filter (fun a : Fin (2 * m) => a < σ a), K (μs a) (μs (σ a)) := by sorry

end DeepLearningTheory
