-- Prove2me | Theorems.Thm_FermiCap_Gaussian_lemma_1
-- name    : FermiCap.Gaussian.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:42:13.934534+00:00
-- url     : https://prove2.me/theorems/b58e7322-a9bc-4995-a176-58258ed6bc38
-- title:
--   Lemma 1 — covariance matrices of even Gaussian states
-- statement:
--   Let $M$ be a real antisymmetric $2n\times2n$ matrix. It is the covariance matrix of an even Gaussian state exactly when
--   $$M^{\mathsf T}M\preceq I.$$
--   Every even Gaussian state with this covariance is pure exactly when $M^{\mathsf T}M=I$. The matrix inequality uses positive-semidefinite order. This characterizes the feasible covariance matrices in the even-Gaussian entropy problem.
-- source:
--   Bravyi, Classical capacity of fermionic product channels, arXiv:quant-ph/0507282v1, p. 5, Lemma 1, eq. (17); covariance on p. 4

import Mathlib
import Definitions.Def_FermiCap_Gaussian_States

noncomputable section
open scoped MatrixOrder ComplexOrder
open Matrix

namespace FermiCap.Gaussian

/-- Lemma 1: admissible real antisymmetric covariances of even Gaussian states,
and the purity criterion for each corresponding state. -/
theorem lemma_1 (n : ℕ) (M : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)
    (hM : Mᵀ = -M) :
    ((∃ ρ : Op n, IsEvenGaussian ρ ∧ covariance ρ = M) ↔
      (1 - Mᵀ * M).PosSemidef) ∧
    (∀ ρ : Op n, IsEvenGaussian ρ → covariance ρ = M →
      (IsPure ρ ↔ Mᵀ * M = 1)) := by sorry

end FermiCap.Gaussian
