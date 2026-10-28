-- Prove2me | Theorems.Thm_AvramDividend_Classical_shifted_future_strip_implies_drawdown_guard
-- name    : AvramDividend.Classical.shifted_future_strip_implies_drawdown_guard
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T18:36:43.156329+00:00
-- url     : https://prove2.me/theorems/5383db5f-9fae-40d9-972a-d1fb55e7ec40
-- title:
--   A future Lévy path confined to a strip has drawdown bounded by the strip width
-- statement:
--   For a fixed past time u and a future horizon T, suppose every shifted future increment through T lies between ε−a and ε. Then at every future time t≤T the running shifted supremum minus the current path value is at most a. This elementary but exact pathwise bridge converts a two-sided raw reserve exit survival event into the reflected drawdown guard needed for killed-record regeneration.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 1; pathwise two-sided-exit-to-reflected-ruin comparison.

import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.shifted_future_strip_implies_drawdown_guard
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a ε : ℝ) (ω : Ω) (u T : ℝ≥0)
    (hUpper : ∀ r : ℝ≥0, r ≤ T →
      X.X (u + r) ω - X.X u ω ≤ ε)
    (hLower : ∀ r : ℝ≥0, r ≤ T →
      ε - a ≤ X.X (u + r) ω - X.X u ω) :
    ∀ t : ℝ≥0, t ≤ T →
      sSup ((fun r : ℝ≥0 => X.X (u + r) ω) '' Set.Icc 0 t) -
        X.X (u + t) ω ≤ a := by sorry
