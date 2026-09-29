-- Prove2me | solution 1 for signed_scalar_centered_sampling_bernstein_lambda_tail_from_kernel_square_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-14T05:20:56.426244+00:00
-- url     : https://prove2.me/submissions/0b9bf354-9004-42a8-8500-002ea80c139a

import Theorems.Thm_scalar_centered_sampling_bernstein_natural_tail_from_quadratic_base_bounds
import Theorems.Thm_signed_scalar_bernstein_lambda_tail_from_unsigned_natural_tail
import Definitions.Def_matrix_completion_neumann

open MatrixCompletion


open MatrixCompletion

/-- Split the signed scalar Bernstein estimate into the unsigned natural-scale
Bernstein theorem and the signed compatibility transfer. -/
theorem solution
    (Centry Cfro Ccompat : ℝ) :
    0 < Centry → 0 < Cfro → 0 < Ccompat →
    ∃ Cpoint cpoint : ℝ, 0 < Cpoint ∧ 0 < cpoint ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (μ₀ sign : ℝ),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ →
        (m : ℝ) ≥
          lam * Real.rpow μ₀ ((4 : ℝ) / 3) *
            (↑(max n₁ n₂)) * Real.rpow (r : ℝ) ((4 : ℝ) / 3) *
              (β * Real.log (↑(max n₁ n₂))) →
        |sign| *
            Real.sqrt (β * Real.log (↑(max n₁ n₂))) *
            Real.rpow
              ((μ₀ * (↑(max n₁ n₂)) * (r : ℝ)) / (m : ℝ))
              ((3 : ℝ) / 2) ≤
          Ccompat * Real.rpow lam (-1) →
        ∀ (Coeff : Finset (Fin n₁ × Fin n₂) → ℝ)
          (B : Matrix (Fin n₁) (Fin n₂) ℝ),
        (∀ Omega : Finset (Fin n₁ × Fin n₂),
          Coeff Omega =
            sign *
              matrixEntrySum
                (centeredSamplingFluctuation Omega
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) B)) →
        entrySupNorm B ≤
          Centry * μ₀ ^ 2 *
            (((r : ℝ) / (↑(max n₁ n₂))) ^ 2) →
        frobeniusNorm B ≤
          Cfro * Real.rpow μ₀ ((3 : ℝ) / 2) *
            Real.rpow ((r : ℝ) / (↑(max n₁ n₂))) ((3 : ℝ) / 2) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              |Coeff Omega| ≤ Cpoint * Real.rpow lam (-1)) ≥
          1 - cpoint * Real.rpow (↑(max n₁ n₂)) (-β) := by
  intro hCentry hCfro hCcompat
  rcases scalar_centered_sampling_bernstein_natural_tail_from_quadratic_base_bounds
      Centry Cfro hCentry hCfro with
    ⟨Cnatural, cnatural, hCnatural, hcnatural, hNatural⟩
  rcases signed_scalar_bernstein_lambda_tail_from_unsigned_natural_tail
      Cnatural cnatural Ccompat hCnatural hcnatural hCcompat with
    ⟨Cpoint, cpoint, hCpoint, hcpoint, hTransfer⟩
  refine ⟨Cpoint, cpoint, hCpoint, hcpoint, ?_⟩
  intro β lam hβ hlam n₁ n₂ r m μ₀ sign
    hn₁ hn₂ hr hm hμ₀ hmLower hCompat Coeff B hRep hEntry hFrob
  have hUnsignedRep :
      ∀ Omega : Finset (Fin n₁ × Fin n₂),
        (fun Omega =>
          matrixEntrySum
            (centeredSamplingFluctuation Omega
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) B)) Omega =
          matrixEntrySum
            (centeredSamplingFluctuation Omega
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) B) := by
    intro Omega
    rfl
  have hUnsignedProb :=
    hNatural β lam hβ hlam n₁ n₂ r m μ₀
      hn₁ hn₂ hr hm hμ₀ hmLower
      (fun Omega =>
        matrixEntrySum
          (centeredSamplingFluctuation Omega
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) B))
      B hUnsignedRep hEntry hFrob
  exact hTransfer β lam hβ hlam n₁ n₂ r m μ₀ sign
    hn₁ hn₂ hr hm hμ₀ hCompat Coeff B hRep hUnsignedProb
