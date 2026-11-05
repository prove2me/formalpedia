-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_strict_interior_eq_countable_rational_band_iUnion
-- name    : AvramDividend.Classical.avram_p3_g_localise_original_strict_interior_eq_countable_rational_band_iUnion
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T13:17:00.361122+00:00
-- url     : https://prove2.me/theorems/a56317f9-6c89-4c32-95dc-ab3719bbafc6
-- title:
--   Original reserve strict cap interior equals countable rational compact C1 band union
-- statement:
--   For the exact original x+X.X-rightLimit D pre-reserve left-limit process, the strict positive-cap interior set equals a countable union over rational pairs (a,b) of interior open band events. Each allowed rational pair has an enlarged compact derivative strip Icc(a/2)b inside the C1 domain. The identity is exact for finite and infinite caps, and gives deterministic countable indexing for predictable localisation without any boundary occupation claim.
-- source:
--   Composes source-exact literal original pre-reserve with accepted P3-G rational band pointwise cover (theorem 3abce49a, pending proof at authoring time).

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_strict_cap_rational_compact_strips_countable_cover

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_g_localise_original_strict_interior_eq_countable_rational_band_iUnion
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (C : ℝ≥0∞) :
    let Z : ℝ≥0 × Ω → ℝ := fun p =>
      Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    ({p : ℝ≥0 × Ω | 0 < Z p ∧ ENNReal.ofReal (Z p) < C} :
       Set (ℝ≥0 × Ω)) =
      ⋃ a : ℚ, ⋃ b : ℚ,
        {p : ℝ≥0 × Ω |
          0 < (a : ℝ) ∧ (a : ℝ) ≤ 2 ∧
          (a : ℝ) ≤ (b : ℝ) ∧
          Icc ((a : ℝ) / 2) (b : ℝ) ⊆
            {v : ℝ | 0 < v ∧ ENNReal.ofReal v < C} ∧
          Z p ∈ Ioo (a : ℝ) (b : ℝ)} := by sorry
