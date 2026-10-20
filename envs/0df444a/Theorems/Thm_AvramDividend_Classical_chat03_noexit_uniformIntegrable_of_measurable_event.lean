-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_noexit_uniformIntegrable_of_measurable_event
-- name    : AvramDividend.Classical.chat03_noexit_uniformIntegrable_of_measurable_event
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T23:02:55.807514+00:00
-- url     : https://prove2.me/theorems/57f3195e-1508-4cef-b8f3-a4444033ade7
-- title:
--   Uniform integrability of no-exit discounted scale payoffs from event measurability
-- statement:
--   If the event that both strict upper and lower passage clocks are infinite is measurable, then all finite-time discounted scale payoffs restricted to that event form a uniformly integrable family in L1. This discharges the earlier proof's separately assumed random-variable measurability, using adaptedness of X at deterministic times, Borel measurability of the official q-scale W including zero, and the accepted bound W(a) on no-exit paths. Does not assume killed scale martingale or stationarity of the stopped payoff.
-- source:
--   Accepted Chat03 scale Borel-measurability and conditional no-exit payoff uniform-integrability lemmas, plus official adaptedness, pinned revision.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_noexit_payoff_family_uniformIntegrable
import Theorems.Thm_AvramDividend_Classical_chat03_scale_function_borel_measurable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_noexit_uniformIntegrable_of_measurable_event
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (hEvent : MeasurableSet
      {ω : Ω | twoSidedExitUpTime X (a - x) ω = ∞ ∧
        twoSidedExitDownTime X (-x) ω = ∞}) :
    UniformIntegrable
      (fun t : ℝ≥0 => fun ω : Ω =>
        if twoSidedExitUpTime X (a - x) ω = ∞ ∧
           twoSidedExitDownTime X (-x) ω = ∞ then
          Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω)
        else 0)
      (1 : ℝ≥0∞) P := by sorry
