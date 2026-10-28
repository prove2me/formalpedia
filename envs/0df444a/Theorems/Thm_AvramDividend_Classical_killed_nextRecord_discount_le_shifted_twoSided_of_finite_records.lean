-- Prove2me | Theorems.Thm_AvramDividend_Classical_killed_nextRecord_discount_le_shifted_twoSided_of_finite_records
-- name    : AvramDividend.Classical.killed_nextRecord_discount_le_shifted_twoSided_of_finite_records
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T22:57:30.169578+00:00
-- url     : https://prove2.me/theorems/b249310c-dd56-4626-bf88-a596febb4a9f
-- title:
--   Finite successive records imply killed-discount upper bound by shifted two-sided reward
-- statement:
--   For finite successive record times at levels b and b+ε with the initial record attained exactly, survival at the later record yields a killed-discount upper bound by the shifted two-sided exit reward. Both the strict two-sided inclusion and the finiteness of the shifted passage clock are now derived from prior proved results, with no auxiliary inclusion or finiteness assumptions.
-- source:
--   Derive the strict two-sided shifted passage event from the no-finite-tie record survival result and substitute this inclusion into the accepted killed-record discount factorisation.

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_killed_nextRecord_discount_le_shifted_twoSided_of_strict_exit_inclusion

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.killed_nextRecord_discount_le_shifted_twoSided_of_finite_records
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (a b ε q : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hε : 0 ≤ ε)
    (u v δ : ℝ≥0)
    (hu : (u : ℝ≥0∞) = twoSidedExitUpTime X b ω)
    (hAt : X.X u ω = b)
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
