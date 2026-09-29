-- Prove2me | solution 1 for rudelson_selection_tangent_deviation_selfbounding_recursion_dense
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-06-23T23:44:14.85274+00:00
-- url     : https://prove2.me/submissions/8251cb22-7f7a-4f25-91d0-e371467e035c

import Theorems.Thm_rudelson_selection_symmetrized_tensor_khintchine_dense
import Theorems.Thm_rudelson_selection_eq21_self_bounding_bridge
import Theorems.Thm_rudelson_selection_expected_deviation_nonneg
import Definitions.Def_matrix_completion_tangent
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

open MatrixCompletion
open scoped Classical BigOperators

set_option maxHeartbeats 1000000

/-
Sketch of bf7a974a (rudelson_selection_tangent_deviation_selfbounding_recursion_dense).
Assembles the three Rudelson 1999 steps:
  child1  EZ ≤ Csym·(sR)·√(EZ+1)               (symmetrization + tensor NC-Khintchine)
  bridge  D ≤ A·√(D+1) ⇒ D ≤ A + A·√D          (eq 2.1, Proved)
  nonneg  0 ≤ EZ                                (Proved)
With A = Csym·(sR), the bridge output A + A·√EZ = Csym·sR + Csym·sR·√EZ is exactly
the target with Csel := Csym. The `0 ≤ EZ` conjunct is the nonneg child.
-/
theorem solution :
    ∃ Csel : ℝ, 0 < Csel ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (S : SVD M r) (R : ℝ),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        0 ≤ R →
        (m : ℝ) ≥ β * (↑(max n₁ n₂)) * (r : ℝ) * Real.log (↑(max n₁ n₂)) →
        (∀ i : Fin n₁, ∀ j : Fin n₂,
          frobeniusNorm (tangentProjection S (coordinateMatrix i j)) ≤ R) →
        (0 ≤ bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              tangentSamplingDeviation Omega S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))))) ∧
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              tangentSamplingDeviation Omega S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
          Csel *
            (Real.sqrt
              (Real.log (↑(max n₁ n₂)) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) * R)
          + Csel *
            (Real.sqrt
              (Real.log (↑(max n₁ n₂)) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) * R) *
            Real.sqrt
              (bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (fun Omega =>
                  tangentSamplingDeviation Omega S
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))))) := by
  obtain ⟨Csym, hCsym_pos, hcore⟩ := rudelson_selection_symmetrized_tensor_khintchine_dense
  refine ⟨Csym, hCsym_pos, ?_⟩
  intro β hβ n₁ n₂ r m M S R hn1 hn2 hr hm hR hdens hcoord
  -- abbreviations
  set p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) with hp_def
  set EZ : ℝ := bernoulliExpectation p
      (fun Omega => tangentSamplingDeviation Omega S p) with hEZ_def
  set A : ℝ := Csym * (Real.sqrt (Real.log (↑(max n₁ n₂)) / p) * R) with hA_def
  -- density forces 0 < p ≤ 1
  have hn1R : (0:ℝ) < (n₁ : ℝ) := by exact_mod_cast hn1
  have hn2R : (0:ℝ) < (n₂ : ℝ) := by exact_mod_cast hn2
  have hmaxpos : 0 < max n₁ n₂ := lt_of_lt_of_le hn1 (le_max_left _ _)
  -- m > 0 from density (RHS > 0): need β>0, max≥1, r>0, log(max)≥0... handle p>0 via m>0
  have hmRle : (m : ℝ) ≤ (n₁ : ℝ) * (n₂ : ℝ) := by
    have h := hm
    have : (m : ℝ) ≤ ((n₁ * n₂ : ℕ) : ℝ) := by exact_mod_cast h
    rw [Nat.cast_mul] at this; exact this
  have hp_le_one : p ≤ 1 := by
    rw [hp_def, div_le_one (by positivity)]; exact hmRle
  have hp_nn : 0 ≤ p := by
    rw [hp_def]; positivity
  -- core gives EZ ≤ A · √(EZ+1)
  have hcore' := hcore β hβ n₁ n₂ r m M S R hn1 hn2 hr hm hR hdens hcoord
  rw [← hp_def, ← hEZ_def, ← hA_def] at hcore'
  -- nonneg child
  have hEZnn : 0 ≤ EZ := by
    rw [hEZ_def]
    exact rudelson_selection_expected_deviation_nonneg S hp_nn hp_le_one
  -- A ≥ 0
  have hA_nn : 0 ≤ A := by
    rw [hA_def]
    exact mul_nonneg (le_of_lt hCsym_pos) (mul_nonneg (Real.sqrt_nonneg _) hR)
  -- bridge : EZ ≤ A + A√EZ
  have hbridge := rudelson_selection_eq21_self_bounding_bridge EZ A hEZnn hA_nn hcore'
  exact ⟨hEZnn, by rw [hA_def] at hbridge; linarith [hbridge]⟩
