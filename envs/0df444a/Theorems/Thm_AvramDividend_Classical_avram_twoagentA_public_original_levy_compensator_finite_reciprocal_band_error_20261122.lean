-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_twoagentA_public_original_levy_compensator_finite_reciprocal_band_error_20261122
-- name    : AvramDividend.Classical.avram_twoagentA_public_original_levy_compensator_finite_reciprocal_band_error_20261122
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T14:12:10.315743+00:00
-- url     : https://prove2.me/theorems/3e20bb12-3f23-4f75-a73a-d6abe32c3199
-- title:
--   Actual original physical finite negative mark source abcf1c3d
-- statement:
--   Reuse already accepted original same-X finite negative physical marked-jump integral proof, with all private original mark and annulus lemmas replaced by the identical publicly proven shared declarations. Source is genuinely original signed mark; no finite total ν hypothesis.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_twoagentA_public_original_levy_signed_mark_band_generic_integrand_finite_annulus_chain_20261122
import Theorems.Thm_AvramDividend_Classical_avram_twoagentA_public_original_levy_single_reciprocal_signed_mark_vs_mass_error_20261122
open MeasureTheory Set AvramDividend.Classical
open scoped Classical NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_twoagentA_public_original_levy_compensator_finite_reciprocal_band_error_20261122
    (ν : Measure ℝ) (n m : ℕ) (hnm : n ≤ m)
    (hMono : Monotone (fun i : ℕ => -(1 / ((i : ℝ) + 1))))
    (hFin : ∀ i ∈ Finset.Ico n m,
      ν (Ioc (-(1 / ((i : ℝ) + 1))) (-(1 / ((i : ℝ) + 2)))) < ⊤)
    (hLin : IntegrableOn (fun z : ℝ => z)
      (Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))) ν) :
    let B : Set ℝ :=
      Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
    let A : ℕ → Set ℝ := fun i =>
      Ioc (-(1 / ((i : ℝ) + 1))) (-(1 / ((i : ℝ) + 2)))
    let c : ℕ → ℝ := fun i => -(1 / ((i : ℝ) + 1))
    let δ : ℕ → ℝ := fun i =>
      1 / ((i : ℝ) + 1) - 1 / ((i : ℝ) + 2)
    |(∫ z in B, z ∂ν) -
      ∑ i ∈ Finset.Ico n m, c i * (ν (A i)).toReal| ≤
      ∑ i ∈ Finset.Ico n m, δ i * (ν (A i)).toReal := by sorry
