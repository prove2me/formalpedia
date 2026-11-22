-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_twoagentA_public_original_reciprocal_band_count_L1_Campbell_20261122
-- name    : AvramDividend.Classical.avram_twoagentA_public_original_reciprocal_band_count_L1_Campbell_20261122
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T14:07:54.17447+00:00
-- url     : https://prove2.me/theorems/c4a7ddd1-f8fc-4720-bf1c-6339004bdbb3
-- title:
--   Original actual signed-mark integral proxy bridge 2149c7ec
-- statement:
--   Source-faithful PUBLIC republishing of an accepted true original negative mark integral bridge, with exact proof and substitution of already Proved PUBLIC dependencies. No new mathematical assumptions introduced.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_twoagentA_shared_original_finite_negative_band_facts
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_anynu_finite_negative_Borel_weighted_past_compensator_real_L1
open MeasureTheory Set AvramDividend.Classical
open scoped Classical NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_twoagentA_public_original_reciprocal_band_count_L1_Campbell_20261122
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n m : ℕ) :
    let B : Set ℝ :=
      Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let N : Ω → ℝ := fun ω => (NX ω (Ioc 0 T ×ˢ B)).toReal
    let r : ℝ := ((T : ℝ≥0∞) * X.ν B).toReal
    Integrable N P ∧ (∫ ω, N ω ∂P) = r := by sorry
