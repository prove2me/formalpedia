-- Prove2me | Theorems.Thm_AvramDividend_Classical_killed_nextRecord_capped_pathwise_shifted_upper
-- name    : AvramDividend.Classical.killed_nextRecord_capped_pathwise_shifted_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T00:08:41.489228+00:00
-- url     : https://prove2.me/theorems/aee4b8b5-9cd5-4d73-bd2b-e029837d5774
-- title:
--   Pathwise higher-record reward dominated by lower-record shifted reward before a finite cap
-- statement:
--   Localise the proved global next-record discount inequality to the event where the higher record occurs before a finite horizon, using monotonicity of upcrossing clocks and survival events.
-- source:
--   Global killed next-record reward domination and passage-time monotonicity

import Theorems.Thm_AvramDividend_Classical_killed_nextRecord_discount_global_shifted_twoSided_upper
import Theorems.Thm_AvramDividend_Classical_killed_higherRecord_survival_implies_lowerRecord_survival_with_measure_import
import Theorems.Thm_AvramDividend_Classical_twoSidedExitUpTime_mono_threshold

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.killed_nextRecord_capped_pathwise_shifted_upper
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (a b ε q : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hε : 0 ≤ ε)
    (N : ℝ≥0) (ρ σ : ℝ≥0∞)
    (hρ : ρ = (⨅ (t : ℝ≥0)
      (_ : ε < X.X ((twoSidedExitUpTime X b ω).toNNReal + t) ω -
          X.X (twoSidedExitUpTime X b ω).toNNReal ω), (t : ℝ≥0∞)))
    (hσ : σ = (⨅ (t : ℝ≥0)
      (_ : X.X ((twoSidedExitUpTime X b ω).toNNReal + t) ω -
          X.X (twoSidedExitUpTime X b ω).toNNReal ω < -a), (t : ℝ≥0∞))) :
    (if twoSidedExitUpTime X (b + ε) ω < barrierRuinTime X a ω ∧
        twoSidedExitUpTime X (b + ε) ω ≤ (N : ℝ≥0∞) then
      ENNReal.ofReal ε *
        ENNReal.ofReal (Real.exp (-(q *
          (twoSidedExitUpTime X (b + ε) ω).toReal)))
      else 0) ≤
    (if twoSidedExitUpTime X b ω < barrierRuinTime X a ω ∧
        twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞) then
      ENNReal.ofReal ε *
        (ENNReal.ofReal (Real.exp (-(q *
          ((twoSidedExitUpTime X b ω).toNNReal : ℝ)))) *
          (if ρ < σ then
            ENNReal.ofReal (Real.exp (-(q * ρ.toReal)))
          else 0))
      else 0) := by sorry
