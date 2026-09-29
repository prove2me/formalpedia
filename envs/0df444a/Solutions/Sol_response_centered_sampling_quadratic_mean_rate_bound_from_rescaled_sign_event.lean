-- Prove2me | solution 1 for response_centered_sampling_quadratic_mean_rate_bound_from_rescaled_sign_event
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-14T05:19:16.928364+00:00
-- url     : https://prove2.me/submissions/022d5084-f92f-4192-b816-2da2f6121d86

import Theorems.Thm_response_centered_sampling_quadratic_mean_unprefactored_rate_bound_from_rescaled_sign_event
import Theorems.Thm_quadratic_mean_response_prefactor_bound_from_unprefactored_rate
import Definitions.Def_matrix_completion_neumann

open MatrixCompletion


open MatrixCompletion

/-- Decompose the quadratic mean response-transfer estimate into the
unprefactored response bound and the deterministic `(1 - p)` prefactor step. -/
theorem solution
    (Cfixed Cresp : ℝ) :
    0 < Cfixed → 0 < Cresp →
    ∃ Cscale : ℝ, 0 < Cscale ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        ∀ (Omega : Finset (Fin n₁ × Fin n₂))
          (Y : Matrix (Fin n₁) (Fin n₂) ℝ)
          (Rop : Matrix (Fin n₁) (Fin n₂) ℝ →
            Matrix (Fin n₁) (Fin n₂) ℝ),
        Y =
          (1 - ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) •
            Rop (centeredSamplingFluctuation Omega
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              ((((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) •
                signMatrix S)) →
        (∀ X : Matrix (Fin n₁) (Fin n₂) ℝ,
          spectralNorm (Rop X) ≤
            Cresp * μ₀ * ((r : ℝ) / (↑(max n₁ n₂))) * spectralNorm X) →
        CenteredSamplingSpectralBound Omega
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            ((((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) •
              signMatrix S)
            (Cfixed * Real.sqrt
              ((β * (↑(max n₁ n₂)) *
                  Real.log (↑(max n₁ n₂))) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
              entrySupNorm
                ((((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) •
                  signMatrix S)) →
        spectralNorm Y ≤
          Cscale * μ₀ * ((r : ℝ) / (↑(max n₁ n₂))) *
            Real.sqrt
              ((β * (↑(max n₁ n₂)) *
                  Real.log (↑(max n₁ n₂))) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
            entrySupNorm
              ((((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) •
                signMatrix S) := by
  intro hCfixed hCresp
  rcases
      response_centered_sampling_quadratic_mean_unprefactored_rate_bound_from_rescaled_sign_event
        Cfixed Cresp hCfixed hCresp with
    ⟨Cunpref, hCunpref, hUnpref⟩
  rcases quadratic_mean_response_prefactor_bound_from_unprefactored_rate
      Cunpref hCunpref with
    ⟨Cpref, hCpref, hPref⟩
  refine ⟨Cpref, hCpref, ?_⟩
  intro β hβ n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ hμ₁
    Omega Y Rop hY hRop hEvent
  let Z : Matrix (Fin n₁) (Fin n₂) ℝ :=
    Rop (centeredSamplingFluctuation Omega
      ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
      ((((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) •
        signMatrix S))
  have hZ :
      spectralNorm Z ≤
        Cunpref * μ₀ * ((r : ℝ) / (↑(max n₁ n₂))) *
          Real.sqrt
            ((β * (↑(max n₁ n₂)) *
                Real.log (↑(max n₁ n₂))) /
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
          entrySupNorm
            ((((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) •
              signMatrix S) := by
    exact hUnpref β hβ n₁ n₂ r m M μ₀ μ₁ S
      hn₁ hn₂ hr hm hμ₀ hμ₁ Omega Z Rop rfl hRop hEvent
  exact hPref β hβ n₁ n₂ r m M μ₀ μ₁ S
    hn₁ hn₂ hr hm hμ₀ hμ₁ Y Z hY hZ
