-- Prove2me | solution 1 for second_order_prefactored_centered_sampling_quadratic_prefactor_bound_from_base_entry_scale
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-06-20T18:48:06.863177+00:00
-- url     : https://prove2.me/submissions/415348e3-73a7-4f56-877e-82ca2902dfa9

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion
open scoped Classical BigOperators

private theorem spectralNorm_smul {n₁ n₂ : Nat} (c : ℝ) (X : Matrix (Fin n₁) (Fin n₂) ℝ) :
    spectralNorm (c • X) = |c| * spectralNorm X := by
  unfold spectralNorm
  rw [map_smul, map_smul, norm_smul, Real.norm_eq_abs]

theorem solution
    (Cfixed Cbase : ℝ) :
    0 < Cfixed → 0 < Cbase →
    ∃ Cpref : ℝ, 0 < Cpref ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (μ₀ : ℝ),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ →
        ∀ (Omega : Finset (Fin n₁ × Fin n₂))
          (B Y : Matrix (Fin n₁) (Fin n₂) ℝ),
        Y =
          ((((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) ^ 2 *
              (1 - 3 * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) +
                3 * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) ^ 2)) •
            centeredSamplingFluctuation Omega
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) B →
        entrySupNorm B ≤
          Cbase * μ₀ ^ 3 * (((r : ℝ) / (↑(max n₁ n₂))) ^ 3) →
        CenteredSamplingSpectralBound Omega
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) B
            (Cfixed * Real.sqrt
              ((β * (↑(max n₁ n₂)) *
                  Real.log (↑(max n₁ n₂))) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
              entrySupNorm B) →
        spectralNorm Y ≤
          Cpref * Cbase *
            |(((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) ^ 2 *
              (1 - 3 * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) +
                3 * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) ^ 2)| *
            μ₀ ^ 3 * (((r : ℝ) / (↑(max n₁ n₂))) ^ 3) *
            Real.sqrt
              ((β * (↑(max n₁ n₂)) *
                  Real.log (↑(max n₁ n₂))) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) := by
  intro hCf hCb
  refine ⟨Cfixed, hCf, ?_⟩
  intro β lam _ _ n₁ n₂ r m μ₀ _ _ _ _ _ Omega B Y hY hEB hSB
  unfold CenteredSamplingSpectralBound at hSB
  rw [hY, spectralNorm_smul]
  set c : ℝ := (((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) ^ 2 *
      (1 - 3 * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) +
        3 * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) ^ 2) with hc
  set sb : ℝ := Real.sqrt ((β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂))) /
      ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) with hsb
  have hfac : 0 ≤ |c| * (Cfixed * sb) := by positivity
  calc |c| * spectralNorm (centeredSamplingFluctuation Omega ((m:ℝ)/((n₁:ℝ)*(n₂:ℝ))) B)
      ≤ |c| * (Cfixed * sb * entrySupNorm B) :=
        mul_le_mul_of_nonneg_left hSB (abs_nonneg _)
    _ = (|c| * (Cfixed * sb)) * entrySupNorm B := by ring
    _ ≤ (|c| * (Cfixed * sb)) * (Cbase * μ₀ ^ 3 * (((r : ℝ) / (↑(max n₁ n₂))) ^ 3)) :=
        mul_le_mul_of_nonneg_left hEB hfac
    _ = Cfixed * Cbase * |c| * μ₀ ^ 3 * (((r : ℝ) / (↑(max n₁ n₂))) ^ 3) * sb := by ring
