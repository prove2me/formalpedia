-- Prove2me | solution 1 for response_centered_sampling_quadratic_mean_unprefactored_rate_bound_from_rescaled_sign_event
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T06:49:33.80953+00:00
-- url     : https://prove2.me/submissions/4adf7950-b0d2-464b-bc6f-91be3dd33009

import Definitions.Def_matrix_completion_neumann

open MatrixCompletion

/-- Unprefactored deterministic response-transfer estimate for the quadratic
mean response. -/
theorem solution
    (Cfixed Cresp : ℝ) :
    0 < Cfixed → 0 < Cresp →
    ∃ Cscale : ℝ, 0 < Cscale ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        let p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))
        let B : Matrix (Fin n₁) (Fin n₂) ℝ := (p⁻¹) • signMatrix S
        ∀ (Omega : Finset (Fin n₁ × Fin n₂))
          (Z : Matrix (Fin n₁) (Fin n₂) ℝ)
          (Rop : Matrix (Fin n₁) (Fin n₂) ℝ →
            Matrix (Fin n₁) (Fin n₂) ℝ),
        Z = Rop (centeredSamplingFluctuation Omega p B) →
        (∀ X : Matrix (Fin n₁) (Fin n₂) ℝ,
          spectralNorm (Rop X) ≤
            Cresp * μ₀ * ((r : ℝ) / (↑(max n₁ n₂))) * spectralNorm X) →
        CenteredSamplingSpectralBound Omega p B
            (Cfixed * Real.sqrt
              ((β * (↑(max n₁ n₂)) *
                  Real.log (↑(max n₁ n₂))) /
                p) *
              entrySupNorm B) →
        spectralNorm Z ≤
          Cscale * μ₀ * ((r : ℝ) / (↑(max n₁ n₂))) *
            Real.sqrt
              ((β * (↑(max n₁ n₂)) *
                  Real.log (↑(max n₁ n₂))) /
                p) *
            entrySupNorm B := by
  intro hCfixed hCresp
  refine ⟨Cresp * Cfixed, mul_pos hCresp hCfixed, ?_⟩
  intro β hβ n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ hμ₁
  dsimp
  intro Omega Z Rop hZ hRop hCentered
  let p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))
  let B : Matrix (Fin n₁) (Fin n₂) ℝ := (p⁻¹) • signMatrix S
  have hmax_pos : 0 < (↑(max n₁ n₂) : ℝ) := by
    exact_mod_cast lt_of_lt_of_le hn₁ (Nat.le_max_left n₁ n₂)
  have hratio_nonneg : 0 ≤ (r : ℝ) / (↑(max n₁ n₂)) := by
    exact div_nonneg (Nat.cast_nonneg _) (le_of_lt hmax_pos)
  have hfactor_nonneg :
      0 ≤ Cresp * μ₀ * ((r : ℝ) / (↑(max n₁ n₂))) := by
    exact mul_nonneg
      (mul_nonneg (le_of_lt hCresp) (le_trans (by norm_num) hμ₀))
      hratio_nonneg
  have hcentered' :
      spectralNorm (centeredSamplingFluctuation Omega p B) ≤
        Cfixed * Real.sqrt
          ((β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂))) / p) *
          entrySupNorm B := by
    simpa [p, B, CenteredSamplingSpectralBound] using hCentered
  calc
    spectralNorm Z =
        spectralNorm (Rop (centeredSamplingFluctuation Omega p B)) := by
          simpa [p, B] using congrArg spectralNorm hZ
    _ ≤ Cresp * μ₀ * ((r : ℝ) / (↑(max n₁ n₂))) *
        spectralNorm (centeredSamplingFluctuation Omega p B) := by
          exact hRop (centeredSamplingFluctuation Omega p B)
    _ ≤ Cresp * μ₀ * ((r : ℝ) / (↑(max n₁ n₂))) *
        (Cfixed * Real.sqrt
          ((β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂))) / p) *
          entrySupNorm B) := by
          exact mul_le_mul_of_nonneg_left hcentered' hfactor_nonneg
    _ =
        (Cresp * Cfixed) * μ₀ * ((r : ℝ) / (↑(max n₁ n₂))) *
          Real.sqrt
            ((β * (↑(max n₁ n₂)) *
                Real.log (↑(max n₁ n₂))) /
              p) *
          entrySupNorm B := by ring
