-- Prove2me | solution 1 for second_order_prefactored_centered_sampling_quadratic_threshold_from_base_entry_scale
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-14T05:03:32.617388+00:00
-- url     : https://prove2.me/submissions/cc847d24-df63-4f10-8dca-d724e095a3a1

import Theorems.Thm_second_order_prefactored_centered_sampling_quadratic_prefactor_bound_from_base_entry_scale
import Theorems.Thm_second_order_quadratic_base_entry_prefactor_absorbed_by_sample_lower
import Definitions.Def_matrix_completion_tangent

open MatrixCompletion


open MatrixCompletion

/-- Decompose the all-equal quadratic centered threshold into the raw
fixed-matrix event bound and scalar absorption of the second-order prefactor. -/
theorem solution
    (Cfixed Cbase : ℝ) :
    0 < Cfixed → 0 < Cbase →
    ∃ Cthreshold : ℝ, 0 < Cthreshold ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (μ₀ : ℝ),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ →
        (m : ℝ) ≥
          lam * Real.rpow μ₀ ((4 : ℝ) / 3) *
            (↑(max n₁ n₂)) * Real.rpow (r : ℝ) ((4 : ℝ) / 3) *
              (β * Real.log (↑(max n₁ n₂))) →
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
          Cthreshold * Real.rpow lam (-((3 : ℝ) / 2)) := by
  intro hCfixed hCbase
  rcases
      second_order_prefactored_centered_sampling_quadratic_prefactor_bound_from_base_entry_scale
        Cfixed Cbase hCfixed hCbase with
    ⟨Cpref, hCpref, hPref⟩
  rcases second_order_quadratic_base_entry_prefactor_absorbed_by_sample_lower
      Cpref Cbase hCpref hCbase with
    ⟨Cthreshold, hCthreshold, hAbsorb⟩
  refine ⟨Cthreshold, hCthreshold, ?_⟩
  intro β lam hβ hlam n₁ n₂ r m μ₀ hn₁ hn₂ hr hm hμ₀
    hmLower Omega B Y hY hEntry hEvent
  exact le_trans
    (hPref β lam hβ hlam n₁ n₂ r m μ₀ hn₁ hn₂ hr hm hμ₀
      Omega B Y hY hEntry hEvent)
    (hAbsorb β lam hβ hlam n₁ n₂ r m μ₀ hn₁ hn₂ hr hm hμ₀ hmLower)
