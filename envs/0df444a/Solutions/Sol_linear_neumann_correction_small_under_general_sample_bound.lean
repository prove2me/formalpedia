-- Prove2me | solution 1 for linear_neumann_correction_small_under_general_sample_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-30T15:43:29.557273+00:00
-- url     : https://prove2.me/submissions/0c9d8c54-3530-409b-a5f8-b26b692f85c2

import Mathlib.Tactic
import Theorems.Thm_linear_neumann_correction_from_diagonal_off_diagonal_bounds
import Theorems.Thm_linear_neumann_diagonal_contribution_under_general_sample_bound
import Theorems.Thm_linear_neumann_off_diagonal_contribution_under_general_sample_bound
import Theorems.Thm_sample_ratio_between_zero_and_one

open MatrixCompletion

/-!
Source: Candès--Recht 2008, PDF p. 20, Lemma 4.5 and equation (4.15), and
PDF pp. 26--29, Section 6.2, equations (6.8)--(6.18).

This is the source-correct theorem-regime proof of the first Neumann
correction.  It no longer factors through the old standalone lambda theorem.
Instead it combines:
* the diagonal contribution under the full Theorem 1.3 sample bound, from
  equations (6.8)--(6.9), Theorem 6.3, and Lemma 6.4;
* the off-diagonal contribution under the same sample bound, from the
  decoupling route (6.12)--(6.18).
-/
theorem solution :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ C' : ℝ, C ≤ C' →
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          C' * max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
                  (μ₀ * Real.rpow (↑(max n₁ n₂)) ((1 : ℝ) / 4))
            * (↑(max n₁ n₂)) * (r : ℝ) * (β * Real.log (↑(max n₁ n₂))) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              NeumannCertificateTermSpectralBound Omega S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) 1 ((1 : ℝ) / 8)) ≥
          1 - c * Real.rpow (↑(max n₁ n₂)) (-β) := by
  rcases linear_neumann_diagonal_contribution_under_general_sample_bound with
    ⟨Cdiag, cdiag, hCdiag, hcdiag, hDiag⟩
  rcases linear_neumann_off_diagonal_contribution_under_general_sample_bound with
    ⟨Coff, coff, hCoff, hcoff, hOff⟩
  let C : ℝ := max Cdiag Coff
  refine ⟨C, cdiag + coff,
    lt_of_lt_of_le hCdiag (le_max_left Cdiag Coff),
    add_pos hcdiag hcoff, ?_⟩
  intro C' hC' β hβ n₁ n₂ r m M μ₀ μ₁ S
    hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
  have hCdiag_le : Cdiag ≤ C' :=
    le_trans (le_max_left Cdiag Coff) hC'
  have hCoff_le : Coff ≤ C' :=
    le_trans (le_max_right Cdiag Coff) hC'
  have hDiagProb :=
    hDiag C' hCdiag_le β hβ n₁ n₂ r m M μ₀ μ₁ S
      hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
  have hOffProb :=
    hOff C' hCoff_le β hβ n₁ n₂ r m M μ₀ μ₁ S
      hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
  have hDiagProb' :
      bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
          (fun Omega =>
            spectralNorm
              (linearNeumannDiagonalContribution Omega S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
              ((1 : ℝ) / 16) * Real.rpow (1 : ℝ) (-1)) ≥
        1 - cdiag * Real.rpow (↑(max n₁ n₂)) (-β) := by
    simpa using hDiagProb
  have hOffProb' :
      bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
          (fun Omega =>
            spectralNorm
              (linearNeumannOffDiagonalContribution Omega S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
              ((1 : ℝ) / 16) * Real.rpow (1 : ℝ) (-1)) ≥
        1 - coff * Real.rpow (↑(max n₁ n₂)) (-β) := by
    simpa using hOffProb
  rcases sample_ratio_between_zero_and_one n₁ n₂ m hn₁ hn₂ hm with
    ⟨hpNonneg, hpLeOne⟩
  have hCorr :=
    linear_neumann_correction_from_diagonal_off_diagonal_bounds S
      ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
      ((1 : ℝ) / 16) ((1 : ℝ) / 16) cdiag coff β 1
      hpNonneg hpLeOne hcdiag hcoff hDiagProb' hOffProb'
  norm_num at hCorr ⊢
  exact hCorr
