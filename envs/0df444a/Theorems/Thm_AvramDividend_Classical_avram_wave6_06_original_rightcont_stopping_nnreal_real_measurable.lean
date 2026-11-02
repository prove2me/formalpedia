-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_rightcont_stopping_nnreal_real_measurable
-- name    : AvramDividend.Classical.avram_wave6_06_original_rightcont_stopping_nnreal_real_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T22:57:03.072832+00:00
-- url     : https://prove2.me/theorems/d12a741a-203c-496d-b0ac-d4baeac33011
-- title:
--   Original right-continuous nonnegative stopping clock is measurable as a real variable
-- statement:
--   Any original nonnegative-real stopping clock for the right-continuous filtration, presented as WithTop NNReal by IsStoppingTime, is an ordinary measurable real-valued random variable. Derive the ENNReal measurability from IsStoppingTime.measurable', invert measurable_coe_nnreal_ennreal_iff and apply Measurable.coe_nnreal_real. This deterministic alignment eliminates the auxiliary random-clock real measurability premise from the inclusive Stieltjes cash bridge, without altering the filtration or adding a probabilistic assumption.
-- source:
--   Mathlib IsStoppingTime.measurable', measurable_coe_nnreal_ennreal_iff and Measurable.coe_nnreal_real at pinned revision; Avram original right-continuous stop.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave6_06_original_rightcont_stopping_nnreal_real_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0))) :
    Measurable (fun ω : Ω => (τ ω : ℝ)) := by sorry
