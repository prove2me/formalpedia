-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_canonical_diffuse_submeasure_null_singletons
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_canonical_diffuse_submeasure_null_singletons
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T21:43:44.321389+00:00
-- url     : https://prove2.me/theorems/ed932eb2-c5d9-4f7d-ad1e-0230b79bd05e
-- title:
--   Literal original dividend Stieltjes diffuse restriction has no singleton mass
-- statement:
--   For every original adapted dividend process, sample path and real time, the genuine Stieltjes dividendMeasure restricted to the complement of its positive singleton masses assigns zero to every singleton. This identifies a canonical atomless measure, independently of a measurable kernel selector and without assuming absent initial or horizon atoms in the original measure.
-- source:
--   Actual source dividendMeasure D and Mathlib Measure.restrict_apply on measurable real singletons. Case analysis distinguishes a positive source payment atom from a zero singleton mass.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_canonical_diffuse_submeasure_null_singletons
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (_hD : IsDividendStrategy 𝓕 D) :
    ∀ (ω : Ω) (t : ℝ),
      ((dividendMeasure D ω).restrict
        {s : ℝ | ¬0 < dividendMeasure D ω {s}}) {t} = 0 := by sorry
