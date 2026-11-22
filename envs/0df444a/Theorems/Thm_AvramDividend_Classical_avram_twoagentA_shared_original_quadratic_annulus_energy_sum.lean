-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_twoagentA_shared_original_quadratic_annulus_energy_sum
-- name    : AvramDividend.Classical.avram_twoagentA_shared_original_quadratic_annulus_energy_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T12:45:53.851916+00:00
-- url     : https://prove2.me/theorems/b139267a-be4d-4a99-a4cf-8695eaa5d5e5
-- title:
--   Original full-activity physical negative mark energy variance bridge (shared)
-- statement:
--   Source-faithful already accepted Worker B physical original-X negative reciprocal mark energy result, with no finite total negative Lévy intensity assumptions. This public theorem enables the unconditional compensated small-jump physical cutoff L2 construction.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_twoagentA_shared_negative_mark_integrated_quadratic_energy
import Theorems.Thm_AvramDividend_Classical_avram_twoagentA_shared_levy_quadratic_annulus_integral_chain
open MeasureTheory Set AvramDividend.Classical
open scoped Classical NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_twoagentA_shared_original_quadratic_annulus_energy_sum
    (ν : Measure ℝ) (n m : ℕ) (hnm : n ≤ m)
    (hMono : Monotone (fun i : ℕ => -(1 / ((i : ℝ) + 1))))
    (hFin : ∀ i ∈ Finset.Ico n m,
      ν (Ioc (-(1 / ((i : ℝ) + 1))) (-(1 / ((i : ℝ) + 2)))) < ⊤)
    (hSq : IntegrableOn (fun z : ℝ => z ^ 2)
      (Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))) ν) :
    let B : Set ℝ :=
      Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
    let A : ℕ → Set ℝ := fun i =>
      Ioc (-(1 / ((i : ℝ) + 1))) (-(1 / ((i : ℝ) + 2)))
    let c : ℕ → ℝ := fun i => -(1 / ((i : ℝ) + 1))
    let δ : ℕ → ℝ := fun i =>
      1 / ((i : ℝ) + 1) - 1 / ((i : ℝ) + 2)
    (∑ i ∈ Finset.Ico n m, δ i * (ν (A i)).toReal) ≤
      2 * (∫ z in B, z ^ 2 ∂ν) ∧
    (∑ i ∈ Finset.Ico n m, c i ^ 2 * (ν (A i)).toReal) ≤
      4 * (∫ z in B, z ^ 2 ∂ν) := by sorry
