-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_01_reflected_record_survival_concat
-- name    : AvramDividend.Classical.avram_wave3_01_reflected_record_survival_concat
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T00:56:01.37877+00:00
-- url     : https://prove2.me/theorems/610e33ed-a233-4e56-8eff-6d3e8de58046
-- title:
--   Source Lévy reflected killed-survival equivalence across consecutive attained upward records
-- statement:
--   For an actual spectrally negative Levy process, let u be an attained first upward passage of b and u+T the attained next upward passage of b+c, with b,c nonnegative. Under the source path boundedness on the stopped prefix, strict survival of the original reflected drawdown barrier a up to u+T holds if and only if the first record survives and the fresh increment-path reflected drawdown stays below a for every t<T. Crucially, the post-record drawdown is represented by the true shifted original path, with its own running supremum. This two-way source equality, using the accepted first-record ruin-prefix equivalence and post-record reset, is the exact pathwise event decomposition required to apply the genuine stopped-history strong Markov product to the killed record survival probability, and thence prove the scale function C1 hazard identity.
-- source:
--   Avram, Palmowski and Pistorius (2007), first-record reflected excursion survival; accepted firstUpcrossing_before_barrierRuin_iff_prefix_survival and firstRecord_drawdown_post_shift_reset.

import Mathlib
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_before_barrierRuin_iff_prefix_survival
import Theorems.Thm_AvramDividend_Classical_firstRecord_drawdown_post_shift_reset

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_01_reflected_record_survival_concat
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b c : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (ω : Ω) (u T : ℝ≥0)
    (hu : (u : ℝ≥0∞) = twoSidedExitUpTime X b ω)
    (hNext : ((u + T : ℝ≥0) : ℝ≥0∞) =
      twoSidedExitUpTime X (b + c) ω)
    (hBdd : BddAbove ((fun r : ℝ≥0 => X.X r ω) '' Icc 0 u)) :
    (((u + T : ℝ≥0) : ℝ≥0∞) < barrierRuinTime X a ω) ↔
      ((u : ℝ≥0∞) < barrierRuinTime X a ω ∧
        ∀ t : ℝ≥0, t < T →
          sSup ((fun r : ℝ≥0 => X.X (u + r) ω) '' Icc 0 t) -
            X.X (u + t) ω ≤ a) := by sorry
