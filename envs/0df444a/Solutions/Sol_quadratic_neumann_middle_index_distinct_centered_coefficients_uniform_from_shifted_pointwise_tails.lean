-- Prove2me | solution 1 for quadratic_neumann_middle_index_distinct_centered_coefficients_uniform_from_shifted_pointwise_tails
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-22T03:16:08.686612+00:00
-- url     : https://prove2.me/submissions/ad3d753f-d5e8-402e-807b-2f374db5cf65

import Mathlib.Data.Fintype.Order
import Definitions.Def_matrix_completion_neumann
import Theorems.Thm_bernoulli_event_probability_mono
import Theorems.Thm_bernoulli_uniform_bound_over_matrix_indices_from_shifted_pointwise_tails
import Theorems.Thm_sample_ratio_between_zero_and_one

open MatrixCompletion

/-!
Source: Candes-Recht 2008, PDF p. 29, the union-bound step after equation
(6.17), and PDF p. 30, equation (6.20), where the repeated-index quadratic
Neumann terms are reduced to coordinate-indexed coefficient events.  This node
repairs the old no-loss uniformization theorem by requiring pointwise tails at
exponent `β + 2`, exactly paying the `n₁ n₂ ≤ n²` coordinate-union loss.
-/

private lemma entrySupNorm_le_of_forall_abs_le {n₁ n₂ : ℕ}
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
    (X : Matrix (Fin n₁) (Fin n₂) ℝ) (B : ℝ)
    (h : ∀ w : Fin n₁ × Fin n₂, |X w.1 w.2| ≤ B) :
    entrySupNorm X ≤ B := by
  haveI : Nonempty (Fin n₁) := Fin.pos_iff_nonempty.mp hn₁
  haveI : Nonempty (Fin n₂) := Fin.pos_iff_nonempty.mp hn₂
  unfold entrySupNorm
  exact ciSup_le fun i => ciSup_le fun j => h (i, j)

theorem solution
    (Cpoint cpoint : ℝ) :
    0 < Cpoint → 0 < cpoint →
    ∃ Ccoef ccoef : ℝ, 0 < Ccoef ∧ 0 < ccoef ∧
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
        (∀ w1 : Fin n₁ × Fin n₂,
          bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (fun Omega2 =>
                |quadraticMiddleIndexDistinctCenteredCoefficientMatrix Omega2 S
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w1.1 w1.2| ≤
                  Cpoint * Real.rpow lam (-1)) ≥
            1 - cpoint * Real.rpow (↑(max n₁ n₂)) (-(β + 2))) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega2 =>
              QuadraticMiddleIndexDistinctCenteredCoefficientBound Omega2 S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (Ccoef * Real.rpow lam (-1))) ≥
          1 - ccoef * Real.rpow (↑(max n₁ n₂)) (-β) := by
  intro hCpoint hcpoint
  rcases bernoulli_uniform_bound_over_matrix_indices_from_shifted_pointwise_tails
      Cpoint cpoint hCpoint hcpoint with
    ⟨Ccoef, ccoef, hCcoef, hccoef, hUniform⟩
  refine ⟨Ccoef, ccoef, hCcoef, hccoef, ?_⟩
  intro β lam hβ _hlam n₁ n₂ r m M μ₀ μ₁ S
    hn₁ hn₂ _hr hm _hμ₀ _hμ₁ _hA0 _hA1 _hmLower hPointwise
  rcases sample_ratio_between_zero_and_one n₁ n₂ m hn₁ hn₂ hm with
    ⟨hp_nonneg, hp_le_one⟩
  let p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))
  let scale : ℝ := Real.rpow lam (-1)
  have hPointwise' :
      ∀ w1 : Fin n₁ × Fin n₂,
        bernoulliEventProb p
            (fun Omega2 =>
              |quadraticMiddleIndexDistinctCenteredCoefficientMatrix Omega2 S
                  p w1.1 w1.2| ≤
                Cpoint * scale) ≥
          1 - cpoint * Real.rpow (↑(max n₁ n₂)) (-(β + 2)) := by
    intro w1
    simpa [p, scale] using hPointwise w1
  have hUniformEvent :
      bernoulliEventProb p
          (fun Omega2 =>
            ∀ w1 : Fin n₁ × Fin n₂,
              |quadraticMiddleIndexDistinctCenteredCoefficientMatrix Omega2 S
                  p w1.1 w1.2| ≤
                Ccoef * scale) ≥
        1 - ccoef * Real.rpow (↑(max n₁ n₂)) (-β) :=
    hUniform β p scale hβ hp_nonneg hp_le_one n₁ n₂ hn₁ hn₂
      (fun w1 Omega2 =>
        quadraticMiddleIndexDistinctCenteredCoefficientMatrix Omega2 S
          p w1.1 w1.2)
      hPointwise'
  have hMono :
      bernoulliEventProb p
          (fun Omega2 =>
            ∀ w1 : Fin n₁ × Fin n₂,
              |quadraticMiddleIndexDistinctCenteredCoefficientMatrix Omega2 S
                  p w1.1 w1.2| ≤
                Ccoef * scale) ≤
        bernoulliEventProb p
          (fun Omega2 =>
            QuadraticMiddleIndexDistinctCenteredCoefficientBound Omega2 S p
              (Ccoef * scale)) := by
    refine bernoulli_event_probability_mono p _ _ hp_nonneg hp_le_one ?_
    intro Omega2 hAll
    exact entrySupNorm_le_of_forall_abs_le hn₁ hn₂
      (quadraticMiddleIndexDistinctCenteredCoefficientMatrix Omega2 S p)
      (Ccoef * scale) hAll
  exact le_trans hUniformEvent hMono
