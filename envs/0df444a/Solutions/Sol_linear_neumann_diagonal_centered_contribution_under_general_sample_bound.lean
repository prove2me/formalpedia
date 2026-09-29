-- Prove2me | solution 1 for linear_neumann_diagonal_centered_contribution_under_general_sample_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-30T15:37:10.453918+00:00
-- url     : https://prove2.me/submissions/e3f9c393-a13b-4a1e-b1ee-1fdd2acb716e

import Mathlib.Tactic
import Theorems.Thm_fixed_matrix_centered_sampling_spectral_bound
import Theorems.Thm_general_sample_bound_implies_lemma66_density_bound
import Theorems.Thm_linear_neumann_diagonal_base_entry_sup_norm_bound_min_dim
import Theorems.Thm_linear_neumann_diagonal_centered_as_fixed_matrix_fluctuation
import Theorems.Thm_linear_neumann_diagonal_centered_fixed_matrix_sampling_transfer_under_general_sample_bound

open MatrixCompletion

namespace MatrixCompletion

private lemma density_bound_implies_fixed_matrix_sample_lower
    {β : ℝ} {n₁ n₂ r m : ℕ} {μ₀ : ℝ}
    (hβ : 2 < β) (hn₁ : 0 < n₁) (_hn₂ : 0 < n₂) (hr : 0 < r)
    (hμ₀ : 1 ≤ μ₀)
    (hdensity :
      (m : ℝ) ≥
        ((8 : ℝ) / 3) * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) *
          (β * Real.log (↑(max n₁ n₂)))) :
    (m : ℝ) ≥
      β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂)) := by
  let N : ℕ := max n₁ n₂
  have hN_pos_nat : 0 < N := by
    dsimp [N]
    exact lt_of_lt_of_le hn₁ (Nat.le_max_left n₁ n₂)
  have hN_ge_one : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr hN_pos_nat)
  have hlog_nonneg : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg hN_ge_one
  have hβ_nonneg : 0 ≤ β := by linarith
  have htail_nonneg : 0 ≤ (N : ℝ) * (β * Real.log (N : ℝ)) := by
    positivity
  have hμ₀_nonneg : 0 ≤ μ₀ := le_trans zero_le_one hμ₀
  have hr_ge_one : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hfactor :
      (1 : ℝ) ≤ ((8 : ℝ) / 3) * μ₀ * (r : ℝ) := by
    have hconst : (1 : ℝ) ≤ (8 : ℝ) / 3 := by norm_num
    have hconst_nonneg : 0 ≤ (8 : ℝ) / 3 := by norm_num
    have hconst_mu : (1 : ℝ) ≤ ((8 : ℝ) / 3) * μ₀ := by
      simpa using mul_le_mul hconst hμ₀ zero_le_one hconst_nonneg
    have hconst_mu_nonneg : 0 ≤ ((8 : ℝ) / 3) * μ₀ :=
      le_trans zero_le_one hconst_mu
    simpa [mul_assoc] using
      mul_le_mul hconst_mu hr_ge_one zero_le_one hconst_mu_nonneg
  have htarget_le_density :
      (N : ℝ) * (β * Real.log (N : ℝ)) ≤
        ((8 : ℝ) / 3) * μ₀ * (N : ℝ) * (r : ℝ) *
          (β * Real.log (N : ℝ)) := by
    have h := mul_le_mul_of_nonneg_right hfactor htail_nonneg
    nlinarith
  exact le_trans (by simpa [N, mul_assoc, mul_left_comm, mul_comm] using htarget_le_density)
    (by simpa [N, mul_assoc, mul_left_comm, mul_comm] using hdensity)

end MatrixCompletion

/-!
Source: Candès--Recht 2008, PDF p. 6, Theorem 1.3/equation (1.9), PDF p. 26,
equation (6.9), PDF p. 27, the display after applying Theorem 6.3 to the
first term in (6.9), and the rectangular convention immediately before
Section 6.1.

The proof follows the paper's diagonal-centered route exactly:
1. rewrite the centered diagonal contribution using equation (6.9);
2. apply Theorem 6.3 to the fixed diagonal base matrix;
3. use the proved rectangular-safe base estimate with `min(n₁,n₂)`;
4. leave the remaining deterministic scalar absorption to the explicit
   transfer child theorem.
-/
theorem solution :
    ∃ Ccenter ccenter : ℝ, 0 < Ccenter ∧ 0 < ccenter ∧
      ∀ C' : ℝ, Ccenter ≤ C' →
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          C' * max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
                  (μ₀ * Real.rpow (↑(max n₁ n₂)) ((1 : ℝ) / 4))
            * (↑(max n₁ n₂)) * (r : ℝ) *
              (β * Real.log (↑(max n₁ n₂))) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              spectralNorm
                (linearNeumannDiagonalCenteredContribution Omega S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
                (1 : ℝ) / 32) ≥
          1 - ccenter * Real.rpow (↑(max n₁ n₂)) (-β) := by
  rcases fixed_matrix_centered_sampling_spectral_bound with
    ⟨Cfixed, hCfixed, hFixed⟩
  rcases general_sample_bound_implies_lemma66_density_bound with
    ⟨Cdensity, hCdensity_pos, hDensity⟩
  rcases linear_neumann_diagonal_base_entry_sup_norm_bound_min_dim with
    ⟨Cbase, hCbase, hBaseBound⟩
  rcases
      linear_neumann_diagonal_centered_fixed_matrix_sampling_transfer_under_general_sample_bound
        Cfixed Cbase hCfixed hCbase with
    ⟨Ctransfer, ccenter, hCtransfer, hccenter, hTransfer⟩
  let Ccenter : ℝ := max Cdensity Ctransfer
  refine ⟨Ccenter, ccenter, ?_, hccenter, ?_⟩
  · exact lt_of_lt_of_le hCdensity_pos (le_max_left Cdensity Ctransfer)
  · intro C' hC' β hβ n₁ n₂ r m M μ₀ μ₁ S
      hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
    have hCdensity_le : Cdensity ≤ C' :=
      le_trans (le_max_left Cdensity Ctransfer) hC'
    have hCtransfer_le : Ctransfer ≤ C' :=
      le_trans (le_max_right Cdensity Ctransfer) hC'
    have hDensityLower :=
      hDensity C' hCdensity_le β hβ n₁ n₂ r m μ₀ μ₁
        hn₁ hn₂ hr hμ₀ hμ₁ hmLower
    have hFixedSample :
        (m : ℝ) ≥
          β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂)) :=
      density_bound_implies_fixed_matrix_sample_lower
        (β := β) (n₁ := n₁) (n₂ := n₂) (r := r) (m := m) (μ₀ := μ₀)
        hβ hn₁ hn₂ hr hμ₀ hDensityLower
    have hFixedProb :=
      hFixed β hβ n₁ n₂ m (linearNeumannDiagonalBaseMatrix S)
        hn₁ hn₂ hm hFixedSample
    have hRep :
        ∀ Omega : Finset (Fin n₁ × Fin n₂),
          linearNeumannDiagonalCenteredContribution Omega S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) =
            (((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹ *
                (1 - 2 * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))))) •
              centeredSamplingFluctuation Omega
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (linearNeumannDiagonalBaseMatrix S) := by
      intro Omega
      exact linear_neumann_diagonal_centered_as_fixed_matrix_fluctuation
        Omega S ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
    have hBase :=
      hBaseBound n₁ n₂ r M μ₀ μ₁ S hn₁ hn₂ hr
        hμ₀ hμ₁ hA0 hA1
    exact hTransfer C' hCtransfer_le β hβ n₁ n₂ r m M μ₀ μ₁ S
      hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower hRep hBase hFixedProb
