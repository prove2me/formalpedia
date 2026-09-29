-- Prove2me | solution 1 for second_order_prefactored_centered_sampling_quadratic_prefactor_bound_from_min_dim_base_entry_scale
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-07-03T23:08:16.454564+00:00
-- url     : https://prove2.me/submissions/84518675-1790-42e0-aaed-d323b288812e

import Definitions.Def_matrix_completion_tangent
import Mathlib.Tactic

open MatrixCompletion

private lemma spectralNorm_smul_le_abs
    {n₁ n₂ : ℕ} (a : ℝ) (X : Matrix (Fin n₁) (Fin n₂) ℝ) :
    spectralNorm (a • X) ≤ |a| * spectralNorm X := by
  unfold spectralNorm
  have hlin :
      LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (a • X)) =
        a • LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin X) := by
    ext v i
    simp [Matrix.toEuclideanLin]
  rw [hlin, norm_smul]
  simp [Real.norm_eq_abs]

/-- Source: Candes-Recht 2008, PDF p. 30, equation (6.21), and the paragraph
immediately after it applying Theorem 6.3 to the first all-equal term.

This direct proof only records the deterministic prefactor bookkeeping: scale
the centered sampling fluctuation by the displayed scalar prefactor, then use
the centered-sampling spectral event and the corrected min-dimension entry
bound. -/
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
          Cbase * μ₀ ^ 3 * (((r : ℝ) / (↑(min n₁ n₂))) ^ 3) →
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
            μ₀ ^ 3 * (((r : ℝ) / (↑(min n₁ n₂))) ^ 3) *
            Real.sqrt
              ((β * (↑(max n₁ n₂)) *
                  Real.log (↑(max n₁ n₂))) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) := by
  intro hCfixed _hCbase
  refine ⟨Cfixed, hCfixed, ?_⟩
  intro β lam _hβ _hlam n₁ n₂ r m μ₀ _hn₁ _hn₂ _hr _hm _hμ₀
    Omega B Y hY hEntry hCentered
  let p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))
  let a : ℝ := (p⁻¹) ^ 2 * (1 - 3 * p + 3 * p ^ 2)
  let s : ℝ :=
    Real.sqrt ((β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂))) / p)
  have hY' : Y = a • centeredSamplingFluctuation Omega p B := by
    simpa [a, p] using hY
  have hS :
      spectralNorm Y ≤ |a| * spectralNorm (centeredSamplingFluctuation Omega p B) := by
    rw [hY']
    exact spectralNorm_smul_le_abs a (centeredSamplingFluctuation Omega p B)
  have hCentered' :
      spectralNorm (centeredSamplingFluctuation Omega p B) ≤ Cfixed * s * entrySupNorm B := by
    simpa [CenteredSamplingSpectralBound, s, p, mul_assoc] using hCentered
  have hStep1 :
      spectralNorm Y ≤ |a| * (Cfixed * s * entrySupNorm B) :=
    le_trans hS (mul_le_mul_of_nonneg_left hCentered' (abs_nonneg a))
  have hFactorNonneg : 0 ≤ |a| * (Cfixed * s) := by
    positivity
  have hStep2 :
      |a| * (Cfixed * s * entrySupNorm B) ≤
        |a| * (Cfixed * s *
          (Cbase * μ₀ ^ 3 * (((r : ℝ) / (↑(min n₁ n₂))) ^ 3))) := by
    have h := mul_le_mul_of_nonneg_left hEntry hFactorNonneg
    simpa [mul_assoc] using h
  calc
    spectralNorm Y ≤ |a| * (Cfixed * s * entrySupNorm B) := hStep1
    _ ≤ |a| * (Cfixed * s *
          (Cbase * μ₀ ^ 3 * (((r : ℝ) / (↑(min n₁ n₂))) ^ 3))) := hStep2
    _ =
        Cfixed * Cbase * |a| * μ₀ ^ 3 *
          (((r : ℝ) / (↑(min n₁ n₂))) ^ 3) * s := by
      ring
