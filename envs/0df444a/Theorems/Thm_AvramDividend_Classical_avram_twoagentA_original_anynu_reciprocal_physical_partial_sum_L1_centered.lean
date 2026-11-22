-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_twoagentA_original_anynu_reciprocal_physical_partial_sum_L1_centered
-- name    : AvramDividend.Classical.avram_twoagentA_original_anynu_reciprocal_physical_partial_sum_L1_centered
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T13:47:13.90895+00:00
-- url     : https://prove2.me/theorems/5fbc2efd-3b19-4f8b-953f-29cedc4ea93e
-- title:
--   Actual original unrestricted-activity finite reciprocal compensated jump partial sum integrable and centred
-- statement:
--   For original physical Lévy X and any finite deterministic horizon, the compensated finite sum of original negative reciprocal marked jump counts has expected value zero and is integrable, without assuming finite total negative Lévy intensity. Each single reciprocal band has finite measure by the original Levy measure truncation, and the proved same-X arbitrary-negative-ν Campbell count compensation gives mean zero. Finite linearity concludes.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_twoagentA_shared_original_finite_negative_band_facts
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_anynu_finite_negative_Borel_mark_compensated_real_L1_centered
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_twoagentA_original_anynu_reciprocal_physical_partial_sum_L1_centered
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ) :
    let B : ℕ → Set ℝ := fun i =>
      Ioc (-(1 / ((i : ℝ) + 1))) (-(1 / ((i : ℝ) + 2)))
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {s : ℝ≥0 |
        0 < s ∧ X.X s ω -
        Function.leftLim (fun t : ℝ≥0 => X.X t ω) s ≠ 0}).map
        (fun s : ℝ≥0 => (s, X.X s ω -
          Function.leftLim (fun t : ℝ≥0 => X.X t ω) s)))
    let r : ℕ → ℝ := fun i =>
      ((T : ℝ≥0∞) * X.ν (B i)).toReal
    let F : Ω → ℝ := fun ω =>
      ∑ i ∈ Finset.range n,
        (-(1 / ((i : ℝ) + 1))) *
          ((NX ω (Ioc 0 T ×ˢ B i)).toReal - r i)
    Integrable F P ∧ (∫ ω, F ω ∂P) = 0 := by sorry
