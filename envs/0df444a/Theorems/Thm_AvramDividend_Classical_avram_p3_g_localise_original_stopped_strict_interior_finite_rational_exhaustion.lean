-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_stopped_strict_interior_finite_rational_exhaustion
-- name    : AvramDividend.Classical.avram_p3_g_localise_original_stopped_strict_interior_finite_rational_exhaustion
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T13:44:27.896309+00:00
-- url     : https://prove2.me/theorems/8746724b-7131-4b6c-a1fb-35c8ec58b05b
-- title:
--   Exact deterministic finite rational band exhaustion of original stopped strict cap interior
-- statement:
--   For the true ruin-truncated clock and original physical prestate, the entire stopped strict interior is the union of events indexed by finite sets of rational intervals whose compact enlargements lie strictly inside the cap. This exact exhaustion is valid even if contact at a finite cap has positive occupation.
-- source:
--   Accepted source exact rational stopped cover 89f6372b and singleton Finset indexing; finite approximation together with independently submitted predictable finite band union 142f2309.

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_stopped_strict_interior_countable_rational_band_union

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_g_localise_original_stopped_strict_interior_finite_rational_exhaustion
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ≥0) :
    let τ : Ω → ℝ≥0 := fun ω =>
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let Z : ℝ≥0 × Ω → ℝ := fun p =>
      Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    ({p : ℝ≥0 × Ω |
        (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
        0 < Z p ∧ ENNReal.ofReal (Z p) < C} : Set (ℝ≥0 × Ω)) =
      ⋃ S : Finset (ℚ × ℚ), ⋃ ab ∈ S,
        {p : ℝ≥0 × Ω |
          (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
          0 < (ab.1 : ℝ) ∧ (ab.1 : ℝ) ≤ 2 ∧
          (ab.1 : ℝ) ≤ (ab.2 : ℝ) ∧
          Icc ((ab.1 : ℝ) / 2) (ab.2 : ℝ) ⊆
            {v : ℝ | 0 < v ∧ ENNReal.ofReal v < C} ∧
          Z p ∈ Ioo (ab.1 : ℝ) (ab.2 : ℝ)} := by sorry
