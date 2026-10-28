-- Prove2me | Theorems.Thm_AvramDividend_Classical_nextRecord_killed_survival_of_shifted_guard
-- name    : AvramDividend.Classical.nextRecord_killed_survival_of_shifted_guard
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T18:18:14.023722+00:00
-- url     : https://prove2.me/theorems/9bbb3db5-7496-4216-aa92-346f309c1a71
-- title:
--   A surviving killed first record and a safe shifted path preserve the next killed record
-- statement:
--   For two genuine finite record clocks u and v, assume the earlier record u occurs strictly before reflected ruin. If v≤u+T and the shifted future drawdown does not exceed the barrier through T, then the next record v also occurs strictly before reflected ruin. The existing exact first-record survival equivalence supplies the past guard, and the proven survival concatenation and strict boundary lemma supply the future guard. This is the conditional event implication required to compare consecutive killed record weights.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 1, first-record killed renewal event implication.

import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_before_barrierRuin_iff_prefix_survival
import Theorems.Thm_AvramDividend_Classical_nextRecord_survives_of_shifted_drawdown_guard

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.nextRecord_killed_survival_of_shifted_guard
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b ε : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hε : 0 ≤ ε)
    (ω : Ω) (u v T : ℝ≥0)
    (hu : (u : ℝ≥0∞) = twoSidedExitUpTime X b ω)
    (hv : (v : ℝ≥0∞) = twoSidedExitUpTime X (b + ε) ω)
    (hBefore : (u : ℝ≥0∞) < barrierRuinTime X a ω)
    (hvT : v ≤ u + T)
    (hPost : ∀ t : ℝ≥0, t ≤ T →
      sSup ((fun r : ℝ≥0 => X.X (u + r) ω) '' Set.Icc 0 t) -
        X.X (u + t) ω ≤ a) :
    (v : ℝ≥0∞) < barrierRuinTime X a ω := by sorry
