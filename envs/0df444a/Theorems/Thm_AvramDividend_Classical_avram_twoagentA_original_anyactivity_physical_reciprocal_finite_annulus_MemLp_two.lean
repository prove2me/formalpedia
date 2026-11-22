-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_twoagentA_original_anyactivity_physical_reciprocal_finite_annulus_MemLp_two
-- name    : AvramDividend.Classical.avram_twoagentA_original_anyactivity_physical_reciprocal_finite_annulus_MemLp_two
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T13:35:51.852666+00:00
-- url     : https://prove2.me/theorems/61770ca1-4742-4672-97c4-ccf11b1086a1
-- title:
--   Original all-activity physical compensated finite negative reciprocal mark annulus is measurable and L2
-- statement:
--   Exact original Lévy X negative marked jump measure, deterministic time horizon, arbitrary negative jump activity and Gaussian component. Prove raw finite reciprocal annular compensated physical count sum is measurable and MemLp 2 using the original raw jump rectangle measurability and the already Proved same-X finite annular square-integrability.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_borel_past_count_raw_measurable
import Theorems.Thm_AvramDividend_Classical_avram_twoagentA_original_allnu_finite_reciprocal_L2_integrable_public
open MeasureTheory Set AvramDividend.Classical
open scoped Classical NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_twoagentA_original_anyactivity_physical_reciprocal_finite_annulus_MemLp_two
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (n m : ℕ) (hnm : n ≤ m) :
    let B : ℕ → Set ℝ := fun i =>
      Ioc (-(1 / ((i : ℝ) + 1))) (-(1 / ((i : ℝ) + 2)))
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let r : ℕ → ℝ := fun i => ((T : ℝ≥0∞) * X.ν (B i)).toReal
    let S : Ω → ℝ := fun ω =>
      ∑ i ∈ Finset.Ico n m,
        (-(1 / ((i : ℝ) + 1))) *
          ((NX ω (Ioc 0 T ×ˢ B i)).toReal - r i)
    Measurable S ∧ MemLp S 2 P := by sorry
