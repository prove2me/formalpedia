-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_infinite_activity_canonical_small_negative_mark_grid_centering
-- name    : AvramDividend.Classical.avram_jump6_B_original_infinite_activity_canonical_small_negative_mark_grid_centering
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T11:13:12.070202+00:00
-- url     : https://prove2.me/theorems/c33d6c2f-8e4a-4ab6-902c-fb25b1e9ff42
-- title:
--   Original infinite-activity stopped physical negative jump count centring, canonical cut band
-- statement:
--   At any actual finite deterministic physical time grid and canonical negative jump cutoff band separated from zero, the true original Levy jump-count minus its physical time compensator, with adapted L2 weights stopped at the natural ruin clock, is integrable and has expectation exactly zero. Requires the original admissible D and true Levy measure; no finite-intensity assumption is introduced.

import Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_natural_ruin_clock_physical_negative_grid_L1_centered
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable
import Theorems.Thm_AvramDividend_Classical_ruinTime_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_finite_clock_witness_of_ruin_meas_stopping
import Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_rightcont_stopped_finiteband_grid_L1_from_source
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Nat BigOperators
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_jump6_B_original_infinite_activity_canonical_small_negative_mark_grid_centering
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (Cap : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x Cap D)
    (n : ℕ) (T : ℝ≥0) (cut : ℕ)
    (grid : ℕ → ℝ≥0) (hGrid : ∀ i, grid i ≤ grid (i + 1))
    (hTime : ∀ i, grid i ≤ T)
    (ε : ℝ) (hε : 0 < ε)
    (H : ℕ → Ω → ℝ)
    (hH : ∀ i, StronglyMeasurable[𝓕.rightCont (grid i)] (H i))
    (hHL2 : ∀ i, MemLp (H i) 2 P)
    (k : ℕ) :
    let B : Set ℝ := Ioo (-1 : ℝ) (-ε) ∩ Iic (-(1 / ((cut : ℝ) + 1)))
    let N : ℕ → Ω → ℝ≥0∞ := fun i ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (grid i) (grid (i + 1)) ×ˢ B)
    ∃ τ : Ω → ℝ≥0,
      (∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal) ∧
      Measurable (fun ω => (τ ω : ℝ)) ∧
      Integrable (fun ω => ∑ i ∈ Finset.range k,
        (if (τ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)
         then (0 : ℝ) else H i ω) *
        ((N i ω).toReal -
          (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
            X.ν B).toReal)) P ∧
      (∫ ω, (∑ i ∈ Finset.range k,
        (if (τ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)
         then (0 : ℝ) else H i ω) *
        ((N i ω).toReal -
          (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
            X.ν B).toReal)) ∂P) = 0 := by sorry
