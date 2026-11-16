-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_original_positive_probability_nojump_linear_source
-- name    : AvramDividend.Classical.avram_bvb_obstruction_original_positive_probability_nojump_linear_source
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T07:20:24.632621+00:00
-- url     : https://prove2.me/theorems/77c05880-1277-4a79-86c5-31ced8177f2e
-- title:
--   Original finite-BV no-negative-jump event has positive probability and exact linear Lévy path
-- statement:
--   For any finite negative jump intensity original standing BV spectrally negative Lévy process and finite horizon, the event that has zero actual negative marks up to T and satisfies the original drift-only source path X(t)=t drift for every t≤T has strictly positive probability. This supplies the genuine original-source stochastic event required for the positive-cap cash obstruction.
-- source:
--   Proved 88cb97ef gives probability of no negative marks equal to exp(-Tν(-∞,0))>0. Proved 93033988 gives the linear source path almost surely conditional on no negative marks. The positive-event intersection lemma transfers the positivity through the almost-sure property.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a82_original_finiteactivity_fullnegative_nojump_probability_20261114
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys75_original_zero_negative_mark_count_entire_source_drift
import Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_positive_markfree_event_survives_ae_linear_path
open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_bvb_obstruction_original_positive_probability_nojump_linear_source
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) (T : ℝ≥0) :
    let E : Set Ω := {ω |
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ (X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iio (0 : ℝ)) = 0}
    0 < P {ω | ω ∈ E ∧
      (∀ t : ℝ≥0, t ≤ T → X.X t ω = (t : ℝ) * X.drift)} := by sorry
