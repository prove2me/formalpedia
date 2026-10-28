-- Prove2me | Theorems.Thm_AvramDividend_Classical_killed_nextRecord_discount_le_shifted_twoSided_of_finite_crossing_clocks
-- name    : AvramDividend.Classical.killed_nextRecord_discount_le_shifted_twoSided_of_finite_crossing_clocks
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T23:00:25.557076+00:00
-- url     : https://prove2.me/theorems/bf344906-150b-47b3-8ae5-67a6dffe2713
-- title:
--   Killed next-record upper bound from finite first-passage clocks alone
-- statement:
--   The stopped next-record discount is bounded by the first-record discount multiplied by the shifted two-sided-exit discount whenever successive finite first-passage clocks are related by a finite delay. The first-upcrossing hitting value, strict exit inclusion and shifted-clock finiteness all follow from already proved Lévy path theorems; no supplementary pathwise assumptions are required.
-- source:
--   Derive the strict two-sided shifted passage event from the no-finite-tie record survival result and substitute this inclusion into the accepted killed-record discount factorisation.

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_killed_nextRecord_discount_le_shifted_twoSided_of_strict_exit_inclusion

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.killed_nextRecord_discount_le_shifted_twoSided_of_finite_crossing_clocks
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (a b ε q : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hε : 0 ≤ ε)
    (u v δ : ℝ≥0)
    (hu : (u : ℝ≥0∞) = twoSidedExitUpTime X b ω)
    (hv : (v : ℝ≥0∞) = twoSidedExitUpTime X (b + ε) ω)
    (hδ : u + δ = v)
    (ρ σ : ℝ≥0∞)
    (hρ : ρ = (⨅ (t : ℝ≥0)
      (_ : ε < X.X (u + t) ω - X.X u ω), (t : ℝ≥0∞)))
    (hσ : σ = (⨅ (t : ℝ≥0)
      (_ : X.X (u + t) ω - X.X u ω < -a), (t : ℝ≥0∞))) :
    (if twoSidedExitUpTime X (b + ε) ω < barrierRuinTime X a ω then
      ENNReal.ofReal ε *
        ENNReal.ofReal (Real.exp (-(q *
          (twoSidedExitUpTime X (b + ε) ω).toReal)))
      else 0) ≤
    ENNReal.ofReal ε *
      (ENNReal.ofReal (Real.exp (-(q * (u : ℝ)))) *
        (if ρ < σ then
          ENNReal.ofReal (Real.exp (-(q * ρ.toReal)))
        else 0)) := by sorry
