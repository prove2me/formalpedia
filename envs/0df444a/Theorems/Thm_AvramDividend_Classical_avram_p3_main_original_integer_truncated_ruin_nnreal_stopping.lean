-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_main_original_integer_truncated_ruin_nnreal_stopping
-- name    : AvramDividend.Classical.avram_p3_main_original_integer_truncated_ruin_nnreal_stopping
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T08:27:16.753489+00:00
-- url     : https://prove2.me/theorems/99c02ca9-ab85-4cf3-a42c-953578c93dfa
-- title:
--   Actual integer-truncated ruin time is a finite bounded right-continuous stopped clock
-- statement:
--   Convert the genuinely Proved original min(ruinTime,n) WithTop stopping-time result into the exact ℝ≥0-valued bounded right-continuous filtration stopped clock that P3-B's original intrinsic compensated C1 jump theorem requires. The clock is the original min(ruinTime X x D ω,n) converted using the certified finite ENNReal toNNReal equivalence. This does not assume a new stopping law or bypass strict ruin terminal conventions.
-- source:
--   Proved original stopped clock bf7c0745; exact pinned ENNReal.toNNReal_mono and ENNReal.coe_toNNReal. Original X, D and rightCont filtration unchanged.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_p3_main_original_integer_truncated_ruin_nnreal_stopping
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (n : ℕ) :
    let τ : Ω → ℝ≥0 := fun ω =>
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal
    (∀ ω, τ ω ≤ (n : ℝ≥0)) ∧
      IsStoppingTime 𝓕.rightCont
        (fun ω => (τ ω : WithTop ℝ≥0)) := by sorry
