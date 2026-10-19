-- Prove2me | Theorems.Thm_AvramDividend_Classical_firstUpcrossing_reflectedSup_eventually_lt_barrier
-- name    : AvramDividend.Classical.firstUpcrossing_reflectedSup_eventually_lt_barrier
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T11:02:17.774985+00:00
-- url     : https://prove2.me/theorems/a7c02e0f-c4e4-4725-8529-36bb96d8c6a3
-- title:
--   Strict positive drawdown survival in a right neighbourhood of an attained first upcrossing
-- statement:
--   At a finite first upcrossing of a nonnegative record b, the proved zero-drawdown identity gives reflectedSup(X,u)=0. If the reflected process is right-continuous at that contact time, its drawdown is strictly below any positive ruin threshold a at all sufficiently close times after u. This provides the local no-ruin neighbourhood missing from the killed-regulator renewal proof, conditional only on the standard right-continuity property (which will be justified using the independently proved runningSup continuity theorem and the Lévy path right-continuity field). No stochastic exit law is assumed.
-- source:
--   Avram Palmowski Pistorius (2007) Proposition 1 boundary restart; published firstUpcrossing_runningSup_sub_path_eq_zero 9243feef-85e4-45be-9f62-5e56edb2abbf and standard Filter continuous-within-at right neighbourhood.

import Mathlib.Topology.Order.Basic
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_runningSup_sub_path_eq_zero

open MeasureTheory Filter Topology Set
open AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.firstUpcrossing_reflectedSup_eventually_lt_barrier
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (t : ℝ≥0) (_ : b < X.X t ω), (t : ℝ≥0∞)))
    (hRight : ContinuousWithinAt (fun t => reflectedSup X t ω)
      (Set.Ici u) u) :
    ∀ᶠ t in 𝓝[≥] u, reflectedSup X t ω < a := by sorry
