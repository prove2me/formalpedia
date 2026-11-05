-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_stopped_strict_interior_countable_rational_band_union
-- name    : AvramDividend.Classical.avram_p3_g_localise_original_stopped_strict_interior_countable_rational_band_union
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T13:23:18.181424+00:00
-- url     : https://prove2.me/theorems/89f6372b-8698-4516-91df-d08e9df3e41e
-- title:
--   Original finite ruin-stopped strict interior equals countable rational compact-strip union
-- statement:
--   For the literal original admissible X.X-rightLimit D pre-reserve and tau=min(ruinTime,T).toNNReal, the inclusive stopped strict positive-cap interior is exactly a countable union indexed by rational interior compact bands. Each enlarged band Icc(a/2)b lies in the C1 domain, and no boundary occupation is dropped. This provides the exact deterministic exhaustion basis needed to localise P3-E jump compensation and P3-F stopped-grid limits.
-- source:
--   Composes Proved P3-G rational band pointwise cover 3abce49a with the exact original ruinTime and pre-reserve leftLimit; no substitute process and no endpoint-limit assumption.

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_strict_cap_rational_compact_strips_countable_cover

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_g_localise_original_stopped_strict_interior_countable_rational_band_union
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
      ⋃ a : ℚ, ⋃ b : ℚ,
        {p : ℝ≥0 × Ω |
          (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
          0 < (a : ℝ) ∧ (a : ℝ) ≤ 2 ∧ (a : ℝ) ≤ (b : ℝ) ∧
          Icc ((a : ℝ) / 2) (b : ℝ) ⊆
            {v : ℝ | 0 < v ∧ ENNReal.ofReal v < C} ∧
          Z p ∈ Ioo (a : ℝ) (b : ℝ)} := by sorry
