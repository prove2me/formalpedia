-- Prove2me | solution 1 for prefactored_centered_sampling_fluctuation_quadratic_threshold_from_mean_entry_scale
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T07:49:48.738757+00:00
-- url     : https://prove2.me/submissions/3b620097-20eb-4081-9932-2bdfcdddafd7

import Theorems.Thm_prefactored_centered_sampling_fluctuation_quadratic_prefactor_bound_from_mean_entry_scale
import Theorems.Thm_quadratic_mean_entry_scale_prefactor_absorbed_by_sample_lower

open MatrixCompletion

/-- Decompose the mean-entry-scale quadratic threshold into the raw
fixed-matrix event bound and scalar sample-size absorption. -/
theorem solution
    (Cfixed Centry : ℝ) :
    0 < Cfixed → 0 < Centry →
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
          (X Y : Matrix (Fin n₁) (Fin n₂) ℝ),
        Y =
          (1 - ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) •
            centeredSamplingFluctuation Omega
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X →
        entrySupNorm X ≤
          Centry * μ₀ ^ 2 *
            (((r : ℝ) / (↑(max n₁ n₂))) ^ 2) *
              (((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) →
        CenteredSamplingSpectralBound Omega
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X
            (Cfixed * Real.sqrt
              ((β * (↑(max n₁ n₂)) *
                  Real.log (↑(max n₁ n₂))) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
              entrySupNorm X) →
        spectralNorm Y ≤
          Cthreshold * Real.rpow lam (-((3 : ℝ) / 2)) := by
  intro hCfixed hCentry
  rcases
      prefactored_centered_sampling_fluctuation_quadratic_prefactor_bound_from_mean_entry_scale
        Cfixed Centry hCfixed hCentry with
    ⟨Cpref, hCpref, hPref⟩
  rcases quadratic_mean_entry_scale_prefactor_absorbed_by_sample_lower
      Cpref Centry hCpref hCentry with
    ⟨Cthreshold, hCthreshold, hAbsorb⟩
  refine ⟨Cthreshold, hCthreshold, ?_⟩
  intro β lam hβ hlam n₁ n₂ r m μ₀ hn₁ hn₂ hr hm hμ₀
    hmLower Omega X Y hY hEntry hEvent
  exact le_trans
    (hPref β lam hβ hlam n₁ n₂ r m μ₀ hn₁ hn₂ hr hm hμ₀
      Omega X Y hY hEntry hEvent)
    (hAbsorb β lam hβ hlam n₁ n₂ r m μ₀ hn₁ hn₂ hr hm hμ₀ hmLower)
