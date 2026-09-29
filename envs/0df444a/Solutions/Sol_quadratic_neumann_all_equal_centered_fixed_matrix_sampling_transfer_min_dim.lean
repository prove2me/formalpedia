-- Prove2me | solution 1 for quadratic_neumann_all_equal_centered_fixed_matrix_sampling_transfer_min_dim
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-07-04T12:43:59.243585+00:00
-- url     : https://prove2.me/submissions/27f530c2-a930-4731-a141-1a6f22e7faf3

import Definitions.Def_matrix_completion_neumann
import Theorems.Thm_quadratic_neumann_all_equal_base_entry_sup_norm_bound_geom_dim
import Theorems.Thm_second_order_prefactored_centered_sampling_quadratic_threshold_from_base_entry_scale_geom_dim
import Theorems.Thm_bernoulli_event_probability_mono

open MatrixCompletion

/-- G4: closes 2421104c by re-deriving the sharp geometric-mean base entry
bound from A0 (ignoring the lossy (r/min)³ hypothesis) and applying the
geometric threshold. -/
theorem solution
    (Cfixed Cbase : ℝ) :
    0 < Cfixed → 0 < Cbase →
    ∃ Ccent ccent : ℝ, 0 < Ccent ∧ 0 < ccent ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          lam * Real.rpow μ₀ ((4 : ℝ) / 3) *
            (↑(max n₁ n₂)) * Real.rpow (r : ℝ) ((4 : ℝ) / 3) *
              (β * Real.log (↑(max n₁ n₂))) →
        (∀ Omega : Finset (Fin n₁ × Fin n₂),
          quadraticNeumannAllEqualCenteredContribution Omega S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) =
            ((((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) ^ 2 *
                (1 - 3 * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) +
                  3 * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) ^ 2)) •
              centeredSamplingFluctuation Omega
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (quadraticNeumannAllEqualBaseMatrix S)) →
        entrySupNorm (quadraticNeumannAllEqualBaseMatrix S) ≤
          Cbase * μ₀ ^ 3 * (((r : ℝ) / (↑(min n₁ n₂))) ^ 3) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              CenteredSamplingSpectralBound Omega
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (quadraticNeumannAllEqualBaseMatrix S)
                (Cfixed * Real.sqrt
                  ((β * (↑(max n₁ n₂)) *
                      Real.log (↑(max n₁ n₂))) /
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                  entrySupNorm (quadraticNeumannAllEqualBaseMatrix S))) ≥
          1 - (1 : ℝ) * Real.rpow (↑(max n₁ n₂)) (-β) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              spectralNorm
                (quadraticNeumannAllEqualCenteredContribution Omega S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
                Ccent * Real.rpow lam (-((3 : ℝ) / 2))) ≥
          1 - ccent * Real.rpow (↑(max n₁ n₂)) (-β) := by
  intro hCf hCb
  obtain ⟨Cb', hCb', hbase⟩ :=
    quadratic_neumann_all_equal_base_entry_sup_norm_bound_geom_dim
  obtain ⟨Cth, hCth, hthr⟩ :=
    second_order_prefactored_centered_sampling_quadratic_threshold_from_base_entry_scale_geom_dim
      Cfixed Cb' hCf hCb'
  refine ⟨Cth, 1, hCth, one_pos, ?_⟩
  intro β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1
    hsample hid hlossy hevent
  have hn₁R : (0 : ℝ) < (n₁ : ℝ) := by exact_mod_cast hn₁
  have hn₂R : (0 : ℝ) < (n₂ : ℝ) := by exact_mod_cast hn₂
  have hp0 : (0 : ℝ) ≤ (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) := by positivity
  have hp1 : (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) ≤ 1 := by
    rw [div_le_one (mul_pos hn₁R hn₂R)]
    calc (m : ℝ) ≤ ((n₁ * n₂ : ℕ) : ℝ) := by exact_mod_cast hm
      _ = (n₁ : ℝ) * (n₂ : ℝ) := by push_cast; ring
  refine le_trans hevent ?_
  apply bernoulli_event_probability_mono _ _ _ hp0 hp1
  intro Omega hOmega
  exact hthr β lam hβ hlam n₁ n₂ r m μ₀ hn₁ hn₂ hr hm hμ₀ hsample Omega
    (quadraticNeumannAllEqualBaseMatrix S) _ (hid Omega)
    (hbase n₁ n₂ r M μ₀ S hn₁ hn₂ hr hμ₀ hA0) hOmega
