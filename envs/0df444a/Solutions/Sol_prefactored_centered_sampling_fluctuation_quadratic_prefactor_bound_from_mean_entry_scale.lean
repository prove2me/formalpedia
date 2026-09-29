-- Prove2me | solution 1 for prefactored_centered_sampling_fluctuation_quadratic_prefactor_bound_from_mean_entry_scale
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-06-20T18:54:13.552013+00:00
-- url     : https://prove2.me/submissions/8275c4cc-f060-4380-b099-5ca259052eca

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion
open scoped Classical BigOperators

private theorem spectralNorm_smul {n₁ n₂ : Nat} (c : ℝ) (X : Matrix (Fin n₁) (Fin n₂) ℝ) :
    spectralNorm (c • X) = |c| * spectralNorm X := by
  unfold spectralNorm
  rw [map_smul, map_smul, norm_smul, Real.norm_eq_abs]

private theorem spectralNorm_nonneg {n₁ n₂ : Nat} (X : Matrix (Fin n₁) (Fin n₂) ℝ) :
    0 ≤ spectralNorm X := by
  unfold spectralNorm; exact norm_nonneg _

theorem solution
    (Cfixed Centry : ℝ) :
    0 < Cfixed → 0 < Centry →
    ∃ Cpref : ℝ, 0 < Cpref ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (μ₀ : ℝ),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ → 1 ≤ μ₀ →
        ∀ (Omega : Finset (Fin n₁ × Fin n₂)) (X Y : Matrix (Fin n₁) (Fin n₂) ℝ),
        Y = (1 - ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) •
            centeredSamplingFluctuation Omega ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X →
        entrySupNorm X ≤
          Centry * μ₀ ^ 2 * (((r : ℝ) / (↑(max n₁ n₂))) ^ 2) *
            (((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) →
        CenteredSamplingSpectralBound Omega ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X
            (Cfixed * Real.sqrt ((β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂))) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) * entrySupNorm X) →
        spectralNorm Y ≤
          Cpref * Centry * |1 - ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))| *
            μ₀ ^ 2 * (((r : ℝ) / (↑(max n₁ n₂))) ^ 2) *
            (((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) *
            Real.sqrt ((β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂))) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) := by
  intro hCf hCe
  refine ⟨Cfixed, hCf, ?_⟩
  intro β lam _ _ n₁ n₂ r m μ₀ _ _ _ _ _ Omega X Y hY hEB hSB
  unfold CenteredSamplingSpectralBound at hSB
  rw [hY, spectralNorm_smul]
  set c : ℝ := 1 - ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) with hc
  set sb : ℝ := Real.sqrt ((β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂))) /
      ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) with hsb
  have hfac : 0 ≤ |c| * (Cfixed * sb) := by positivity
  calc |c| * spectralNorm (centeredSamplingFluctuation Omega ((m:ℝ)/((n₁:ℝ)*(n₂:ℝ))) X)
      ≤ |c| * (Cfixed * sb * entrySupNorm X) := mul_le_mul_of_nonneg_left hSB (abs_nonneg _)
    _ = (|c| * (Cfixed * sb)) * entrySupNorm X := by ring
    _ ≤ (|c| * (Cfixed * sb)) *
          (Centry * μ₀ ^ 2 * (((r : ℝ) / (↑(max n₁ n₂))) ^ 2) *
            (((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹)) := mul_le_mul_of_nonneg_left hEB hfac
    _ = Cfixed * Centry * |c| * μ₀ ^ 2 * (((r : ℝ) / (↑(max n₁ n₂))) ^ 2) *
          (((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) * sb := by ring
