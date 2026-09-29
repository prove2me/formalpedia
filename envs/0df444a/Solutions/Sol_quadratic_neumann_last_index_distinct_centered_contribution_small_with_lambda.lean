-- Prove2me | solution 1 for quadratic_neumann_last_index_distinct_centered_contribution_small_with_lambda
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-07-04T13:32:28.278244+00:00
-- url     : https://prove2.me/submissions/8ac44b84-29bb-40b1-aff2-2ec44f2b76a2

import Definitions.Def_matrix_completion_neumann
import Theorems.Thm_quadratic_neumann_last_index_distinct_centered_coefficient_entry_sup_event_tight_min_dim
import Theorems.Thm_fixed_matrix_centered_sampling_spectral_bound
import Theorems.Thm_quadratic_neumann_sample_lower_implies_fixed_matrix_sample_lower
import Theorems.Thm_sample_ratio_between_zero_and_one
import Theorems.Thm_bernoulli_event_probability_mono
import Theorems.Thm_bernoulli_pair_event_probability_from_marginal_and_conditional_lower_bounds_of_nonneg
import Theorems.Thm_entry_sup_norm_sign_matrix_bound_from_a0_geom_dim
import Theorems.Thm_quadratic_neumann_last_index_distinct_centered_decoupled_as_coefficient_fluctuation
import Theorems.Thm_quadratic_neumann_last_index_distinct_centered_decoupling_transfer
import Theorems.Thm_quadratic_neumann_first_index_distinct_centered_decoupled_threshold_from_tight_coefficient_scale
import Mathlib.Data.Fintype.Order

open MatrixCompletion

/-- Honest closure of the centered `ω₁ = ω₂ ≠ ω₃` quadratic Neumann term
(Candès–Recht 2008 §6.3, Lemma 6.7 after the ξ² expansion):

* the tight coefficient event (`..._coefficient_entry_sup_event_tight_min_dim`)
  is instantiated at `μ₁ := μ₀ √r`, legal by the geometric-mean Cauchy–Schwarz
  bridge `entry_sup_norm_sign_matrix_bound_from_a0_geom_dim`;
* Theorem 6.3 (`fixed_matrix_centered_sampling_spectral_bound`) controls the
  outer centered sampling of the conditional coefficient matrix;
* the generic deterministic threshold node (proved for the first-index branch,
  stated for a FREE coefficient matrix `B`, hence branch-independent) absorbs
  prefactor × 6.3-factor × tight scale into `Cth·λ^{-3/2}` under the §6.3
  sample bound;
* the generic Bernoulli pair assembler and the proved decoupling transfer
  land the coupled single-`Ω` event. -/
theorem solution :
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
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              spectralNorm
                (quadraticNeumannLastIndexDistinctCenteredContribution Omega S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
                Ccent * Real.rpow lam (-((3 : ℝ) / 2))) ≥
          1 - ccent * Real.rpow (↑(max n₁ n₂)) (-β) := by
  obtain ⟨Ccoef, ccoef, hCcoef0, hccoef0, hcoef⟩ :=
    quadratic_neumann_last_index_distinct_centered_coefficient_entry_sup_event_tight_min_dim
  obtain ⟨Cfix, hCfix0, hfix⟩ := fixed_matrix_centered_sampling_spectral_bound
  obtain ⟨Cth, hCth0, hth⟩ :=
    quadratic_neumann_first_index_distinct_centered_decoupled_threshold_from_tight_coefficient_scale
      Cfix Ccoef hCfix0 hCcoef0
  obtain ⟨Cdcp, cdcp, hCdcp0, hcdcp0, htrans⟩ :=
    quadratic_neumann_last_index_distinct_centered_decoupling_transfer
  refine ⟨Cdcp * Cth, cdcp * (1 + ccoef), mul_pos hCdcp0 hCth0,
    mul_pos hcdcp0 (by linarith), ?_⟩
  intro β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hsample
  obtain ⟨hp0, hp1⟩ := sample_ratio_between_zero_and_one n₁ n₂ m hn₁ hn₂ hm
  have hrR1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hrR0 : (0 : ℝ) < (r : ℝ) := lt_of_lt_of_le one_pos hrR1
  have hμ₀0 : (0 : ℝ) < μ₀ := lt_of_lt_of_le one_pos hμ₀
  have hN0 : (0 : ℝ) < (↑(max n₁ n₂) : ℝ) := by
    have h := lt_of_lt_of_le hn₁ (le_max_left n₁ n₂)
    exact_mod_cast h
  -- μ₁ := μ₀·√r is a legal A1 parameter, by the A0 geometric-mean bridge
  have hsr1 : (1 : ℝ) ≤ Real.sqrt (r : ℝ) := Real.one_le_sqrt.mpr hrR1
  have hμ₁' : (1 : ℝ) ≤ μ₀ * Real.sqrt (r : ℝ) := by
    calc (1 : ℝ) = 1 * 1 := (one_mul 1).symm
      _ ≤ μ₀ * Real.sqrt (r : ℝ) :=
          mul_le_mul hμ₀ hsr1 zero_le_one (le_trans zero_le_one hμ₀)
  have hA1' : A1 S (μ₀ * Real.sqrt (r : ℝ)) := by
    have hsup := entry_sup_norm_sign_matrix_bound_from_a0_geom_dim
      n₁ n₂ r M μ₀ S hn₁ hn₂ hr hμ₀ hA0
    have hmulself : Real.sqrt (r : ℝ) * Real.sqrt (r : ℝ) = (r : ℝ) :=
      Real.mul_self_sqrt (le_of_lt hrR0)
    have halg : (μ₀ * Real.sqrt (r : ℝ)) *
        (Real.sqrt (r : ℝ) / Real.sqrt ((n₁ : ℝ) * (n₂ : ℝ))) =
        μ₀ * (r : ℝ) / Real.sqrt ((n₁ : ℝ) * (n₂ : ℝ)) := by
      rw [show (μ₀ * Real.sqrt (r : ℝ)) *
          (Real.sqrt (r : ℝ) / Real.sqrt ((n₁ : ℝ) * (n₂ : ℝ))) =
          μ₀ * (Real.sqrt (r : ℝ) * Real.sqrt (r : ℝ)) /
            Real.sqrt ((n₁ : ℝ) * (n₂ : ℝ)) from by ring,
        hmulself]
    intro i j
    have hij : |signMatrix S i j| ≤ entrySupNorm (signMatrix S) := by
      have h1 : |signMatrix S i j| ≤ ⨆ j' : Fin n₂, |signMatrix S i j'| :=
        Finite.le_ciSup (f := fun j' : Fin n₂ => |signMatrix S i j'|) j
      have h2 : (⨆ j' : Fin n₂, |signMatrix S i j'|) ≤
          ⨆ i' : Fin n₁, ⨆ j' : Fin n₂, |signMatrix S i' j'| :=
        Finite.le_ciSup
          (f := fun i' : Fin n₁ => ⨆ j' : Fin n₂, |signMatrix S i' j'|) i
      calc |signMatrix S i j| ≤ ⨆ j' : Fin n₂, |signMatrix S i j'| := h1
        _ ≤ ⨆ i' : Fin n₁, ⨆ j' : Fin n₂, |signMatrix S i' j'| := h2
        _ = entrySupNorm (signMatrix S) := rfl
    calc |signMatrix S i j|
        ≤ entrySupNorm (signMatrix S) := hij
      _ ≤ μ₀ * (r : ℝ) / Real.sqrt ((n₁ : ℝ) * (n₂ : ℝ)) := hsup
      _ = (μ₀ * Real.sqrt (r : ℝ)) *
          Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) := by
          rw [Real.sqrt_div (le_of_lt hrR0)]
          exact halg.symm
  -- marginal: the tight coefficient event at μ₁ := μ₀·√r
  have hmarg := hcoef β hβ n₁ n₂ r m M μ₀ (μ₀ * Real.sqrt (r : ℝ)) S
    hn₁ hn₂ hr hm hμ₀ hμ₁' hA0 hA1'
  -- Theorem 6.3's sample hypothesis
  have hmfix : (m : ℝ) ≥
      β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂)) :=
    quadratic_neumann_sample_lower_implies_fixed_matrix_sample_lower
      β lam n₁ n₂ r m μ₀ hβ hlam hn₁ hn₂ hr hμ₀ hsample
  -- conditional: Theorem 6.3 on the fixed coefficient matrix + threshold
  have hcond : ∀ Omega3 : Finset (Fin n₁ × Fin n₂),
      QuadraticLastIndexDistinctCenteredCoefficientBound Omega3 S
        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
        (Ccoef *
          (Real.sqrt
              (((β + 2) * Real.log (↑(max n₁ n₂))) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
              (μ₀ * Real.sqrt (r : ℝ) *
                Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                  Real.sqrt (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) *
                    (μ₀ * (r : ℝ) / (↑(min n₁ n₂)))) +
            (((β + 2) * Real.log (↑(max n₁ n₂))) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
              (μ₀ * Real.sqrt (r : ℝ) *
                Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                  (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) *
                    (μ₀ * (r : ℝ) / (↑(min n₁ n₂)))))) →
      bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
          (fun Omega1 =>
            spectralNorm
              (quadraticNeumannLastIndexDistinctCenteredDecoupledContribution
                Omega1 Omega3 S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
              Cth * Real.rpow lam (-((3 : ℝ) / 2))) ≥
        1 - 1 * Real.rpow (↑(max n₁ n₂)) (-β) := by
    intro Omega3 hcoefbound
    have h63 := hfix β hβ n₁ n₂ m
      (quadraticLastIndexDistinctCenteredCoefficientMatrix Omega3 S
        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))))
      hn₁ hn₂ hm hmfix
    have himp : ∀ Omega1 : Finset (Fin n₁ × Fin n₂),
        CenteredSamplingSpectralBound Omega1
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
          (quadraticLastIndexDistinctCenteredCoefficientMatrix Omega3 S
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))))
          (Cfix * Real.sqrt
            ((β * (↑(max n₁ n₂)) *
                Real.log (↑(max n₁ n₂))) /
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
            entrySupNorm
              (quadraticLastIndexDistinctCenteredCoefficientMatrix Omega3 S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))))) →
        spectralNorm
          (quadraticNeumannLastIndexDistinctCenteredDecoupledContribution
            Omega1 Omega3 S
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
          Cth * Real.rpow lam (-((3 : ℝ) / 2)) := by
      intro Omega1 hev
      exact hth β lam hβ hlam n₁ n₂ r m μ₀ hn₁ hn₂ hr hm hμ₀ hsample Omega1
        (quadraticLastIndexDistinctCenteredCoefficientMatrix Omega3 S
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))))
        (quadraticNeumannLastIndexDistinctCenteredDecoupledContribution
          Omega1 Omega3 S ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))))
        (quadratic_neumann_last_index_distinct_centered_decoupled_as_coefficient_fluctuation
          Omega1 Omega3 S ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))))
        hcoefbound hev
    have hmono := bernoulli_event_probability_mono
      ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
      (fun Omega1 =>
        CenteredSamplingSpectralBound Omega1
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
          (quadraticLastIndexDistinctCenteredCoefficientMatrix Omega3 S
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))))
          (Cfix * Real.sqrt
            ((β * (↑(max n₁ n₂)) *
                Real.log (↑(max n₁ n₂))) /
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
            entrySupNorm
              (quadraticLastIndexDistinctCenteredCoefficientMatrix Omega3 S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))))))
      (fun Omega1 =>
        spectralNorm
          (quadraticNeumannLastIndexDistinctCenteredDecoupledContribution
            Omega1 Omega3 S
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
          Cth * Real.rpow lam (-((3 : ℝ) / 2)))
      hp0 hp1 himp
    exact le_trans h63 hmono
  -- pair event via the generic Bernoulli pair assembler
  have hcondscale : (0 : ℝ) ≤ 1 * Real.rpow (↑(max n₁ n₂)) (-β) := by
    rw [one_mul]
    exact le_of_lt (Real.rpow_pos_of_pos hN0 (-β))
  have hpair : bernoulliPairEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
      (fun Omega1 Omega3 =>
        spectralNorm
          (quadraticNeumannLastIndexDistinctCenteredDecoupledContribution
            Omega1 Omega3 S
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
          Cth * Real.rpow lam (-((3 : ℝ) / 2))) ≥
      1 - (1 + ccoef) * Real.rpow (↑(max n₁ n₂)) (-β) :=
    bernoulli_pair_event_probability_from_marginal_and_conditional_lower_bounds_of_nonneg
      ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) ccoef 1
      (Real.rpow (↑(max n₁ n₂)) (-β)) _ _
      hp0 hp1 hcondscale hmarg hcond
  -- decoupling transfer: pair model → coupled single-Ω model
  exact htrans S ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) Cth (1 + ccoef) β lam
    hp0 hp1 hCth0 (by linarith) hpair
