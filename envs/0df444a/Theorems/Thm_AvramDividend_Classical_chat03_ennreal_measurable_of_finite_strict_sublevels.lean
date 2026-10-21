-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_ennreal_measurable_of_finite_strict_sublevels
-- name    : AvramDividend.Classical.chat03_ennreal_measurable_of_finite_strict_sublevels
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T07:13:04.661341+00:00
-- url     : https://prove2.me/theorems/0cae547a-685f-4f99-bc65-83fd64d3cad7
-- title:
--   Measurability of an extended nonnegative-valued clock from every finite strict sublevel event
-- statement:
--   For any extended nonnegative-real-valued random clock f, if the event f<t is measurable for every finite nonnegative threshold t, then f is a measurable random variable taking values in ENNReal, including the value infinity. The proof identifies the event f<infinity with the countable union over natural n of f<n, using the Archimedean cofinality of natural thresholds among finite ENNReal elements. Measurability on all open initial intervals follows, so the standard Borel characterisation yields Measurable f. No stopping-time or Lévy-specific assumptions are required.
-- source:
--   Pinned Mathlib measurable_of_Iio, ENNReal.forall_ennreal and ENNReal.exists_nat_gt, and countable measurable unions.

import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Data.ENNReal.Basic

open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat03_ennreal_measurable_of_finite_strict_sublevels
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (f : Ω → ℝ≥0∞)
    (h : ∀ t : ℝ≥0,
      MeasurableSet {ω : Ω | f ω < (t : ℝ≥0∞)}) :
    Measurable f := by sorry
