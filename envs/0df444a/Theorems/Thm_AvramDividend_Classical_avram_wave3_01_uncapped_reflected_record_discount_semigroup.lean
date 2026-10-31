-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_01_uncapped_reflected_record_discount_semigroup
-- name    : AvramDividend.Classical.avram_wave3_01_uncapped_reflected_record_discount_semigroup
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T08:01:27.184413+00:00
-- url     : https://prove2.me/theorems/3890ee9b-06d2-4898-8781-80440cbfd0bf
-- title:
--   Actual original Lévy discounted reflected-killed first-record survival has an uncapped multiplicative renewal law
-- statement:
--   For a genuine spectrally negative Lévy process, the q-discounted probability that the original strict upward first-record at b+c occurs before strict reflected-drawdown ruin at depth a equals the product of the corresponding b and c killed record expectations. All clocks are original source first hitting-time infima, no Standing/C1 hypotheses, b,c,a,q positive. The proof must use no positive upward overshoot, exact pathwise record/survival concatenation, finite stopped strong Markov for the capped record, the accepted shifted true Borel clock equality, and monotone convergence as the cap increases. This is the decisive source-specific probabilistic prerequisite for continuous record hazard and pure jump scale-function C1.
-- source:
--   Source-first record T_(b+c) addition 794e45f9; reflected survival concatenation 610e33ed,b34816aa,e8b117ec; finite capped reflected reward strong Markov c97558ac; source exact future pair clocks acce5dd9; canonical reflection and two-sided-exit definitions; WSMission root cd61d678 C1 path.

import Mathlib
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_01_uncapped_reflected_record_discount_semigroup
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b c q : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hq : 0 < q) :
    (∫⁻ ω, if twoSidedExitUpTime X (b + c) ω < barrierRuinTime X a ω then
    ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X (b + c) ω).toReal)))
  else 0 ∂P) =
      (∫⁻ ω, if twoSidedExitUpTime X b ω < barrierRuinTime X a ω then
    ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X b ω).toReal)))
  else 0 ∂P) *
      (∫⁻ ω, if twoSidedExitUpTime X c ω < barrierRuinTime X a ω then
    ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X c ω).toReal)))
  else 0 ∂P) := by sorry
