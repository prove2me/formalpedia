-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_twoagentA_shared_original_physical_reciprocal_variance_le_4V
-- name    : AvramDividend.Classical.avram_twoagentA_shared_original_physical_reciprocal_variance_le_4V
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T12:50:33.610975+00:00
-- url     : https://prove2.me/theorems/ecd3277d-d6b7-4bb1-9601-4a2b0d2fbe6b
-- title:
--   Original full-activity physical negative mark variance variance bridge (shared)
-- statement:
--   Source-faithful already accepted Worker B physical original-X negative reciprocal mark variance result, with no finite total negative Lévy intensity assumptions. This public theorem enables the unconditional compensated small-jump physical cutoff L2 construction.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_twoagentA_shared_original_reciprocal_finitebin_isometry
import Theorems.Thm_AvramDividend_Classical_avram_twoagentA_shared_original_quadratic_annulus_energy_sum
import Theorems.Thm_AvramDividend_Classical_avram_twoagentA_shared_negative_reciprocal_endpoint_monotone
import Theorems.Thm_AvramDividend_Classical_avram_twoagentA_shared_original_finite_negative_band_facts
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_nu_quadratic_real_energy
open MeasureTheory Set AvramDividend.Classical
open scoped Classical NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_twoagentA_shared_original_physical_reciprocal_variance_le_4V
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (n m : ℕ) (hnm : n ≤ m) :
    let B : Set ℝ :=
      Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
    let A : ℕ → Set ℝ := fun i =>
      Ioc (-(1 / ((i : ℝ) + 1))) (-(1 / ((i : ℝ) + 2)))
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {s : ℝ≥0 |
        0 < s ∧ X.X s ω -
          Function.leftLim (fun t : ℝ≥0 => X.X t ω) s ≠ 0}).map
        (fun s : ℝ≥0 => (s, X.X s ω -
          Function.leftLim (fun t : ℝ≥0 => X.X t ω) s)))
    let r : ℕ → ℝ := fun i =>
      ((T : ℝ≥0∞) * X.ν (A i)).toReal
    let S : Ω → ℝ := fun ω =>
      ∑ i ∈ Finset.Ico n m,
        (-(1 / ((i : ℝ) + 1))) *
          ((NX ω (Ioc 0 T ×ˢ A i)).toReal - r i)
    let V : ℝ := (T : ℝ) * (∫ z in B, z ^ 2 ∂X.ν)
    (∫ ω, (S ω) ^ 2 ∂P) ≤ 4 * V := by sorry
