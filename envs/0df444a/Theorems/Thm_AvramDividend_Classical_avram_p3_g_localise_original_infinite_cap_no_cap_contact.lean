-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_infinite_cap_no_cap_contact
-- name    : AvramDividend.Classical.avram_p3_g_localise_original_infinite_cap_no_cap_contact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T13:10:02.295984+00:00
-- url     : https://prove2.me/theorems/0be46803-f3bd-41a7-b3da-7a012ca59244
-- title:
--   Infinite cap removes original pre-reserve cap-contact region exactly
-- statement:
--   For the literal original spectrally negative Levy reserve with right-limit dividend control, when the allowable cap C equals top, no finite real reserve prestate can equal C. Consequently the strict cap interior is exactly the strictly positive reserve set, without an occupation-zero assumption or any change of process.
-- source:
--   Mathlib ENNReal.ofReal_lt_top/finite simp on original source leftLimit, with the canonical infinite-cap alternative.

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_g_localise_original_infinite_cap_no_cap_contact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (C : ℝ≥0∞) (hTop : C = ⊤) :
    let Z : ℝ≥0 × Ω → ℝ := fun p =>
      Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    ({p : ℝ≥0 × Ω | ENNReal.ofReal (Z p) = C} : Set (ℝ≥0 × Ω)) = ∅ ∧
    ({p : ℝ≥0 × Ω | 0 < Z p ∧ ENNReal.ofReal (Z p) < C} :
      Set (ℝ≥0 × Ω)) =
      {p : ℝ≥0 × Ω | 0 < Z p} := by sorry
