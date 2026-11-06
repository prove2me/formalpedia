-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_double_min_toNNReal_clock_rightcont_stopping
-- name    : AvramDividend.Classical.avram_sweep16_original_double_min_toNNReal_clock_rightcont_stopping
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T18:26:43.915357+00:00
-- url     : https://prove2.me/theorems/35c40640-9224-4cd4-aa51-ae9cafe1d984
-- title:
--   Original finite double-min local ruin clock converted to NNReal remains an exact right-continuous stopping time
-- statement:
--   The same physical doubly stopped min(ruinTime,n,S_k) is proved finite with literal NNReal-to-ENNReal identity; the extended clock is already a Proved original-filtration stopping time. Rewrite the clock functions extensionally and transport the stopping-time property to the exact NNReal cutoff used by genuine stochastic source theorems, preserving the original process and filtration.
-- source:
--   Verified original double-min literal clock bounds and original double-min stopping-time closure; depends only on these fresh SWEEP16 source theorems.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_double_min_clock_literal_extended_bounds
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_double_min_clock_rightcont_stopping
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_sweep16_original_double_min_toNNReal_clock_rightcont_stopping
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (S : ℕ → Ω → ℝ≥0∞)
    (hSstop : ∀ k, IsStoppingTime 𝓕.rightCont (S k)) :
    ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => ((min (min (ruinTime X x D ω) (n : ℝ≥0∞))
        (S k ω)).toNNReal : WithTop ℝ≥0)) := by sorry
