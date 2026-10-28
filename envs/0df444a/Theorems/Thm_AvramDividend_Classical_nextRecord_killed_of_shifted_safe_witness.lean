-- Prove2me | Theorems.Thm_AvramDividend_Classical_nextRecord_killed_of_shifted_safe_witness
-- name    : AvramDividend.Classical.nextRecord_killed_of_shifted_safe_witness
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T18:31:13.003368+00:00
-- url     : https://prove2.me/theorems/ce4bca1e-9d20-4b16-b443-d69431b318ed
-- title:
--   A safe future path with a strictly higher witness produces a surviving next record
-- statement:
--   Starting at an attained finite first upward record u strictly before reflected ruin, assume the future Lévy increment at u+T exceeds ε and the shifted future drawdown stays within the ruin barrier throughout [0,T]. Then the actual first crossing of level b+ε is finite, occurs no later than u+T, and precedes reflected ruin. This transfers a future-path Markov survival and upper-exit event into the original process's killed first-record indicator.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 1; pathwise witness-to-killed-record transfer.

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_nextRecord_upclock_le_shifted_witness
import Theorems.Thm_AvramDividend_Classical_nextRecord_killed_survival_of_shifted_guard

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.nextRecord_killed_of_shifted_safe_witness
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b ε : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hε : 0 ≤ ε)
    (ω : Ω) (u T : ℝ≥0)
    (hu : (u : ℝ≥0∞) = twoSidedExitUpTime X b ω)
    (hAt : X.X u ω = b)
    (hBefore : (u : ℝ≥0∞) < barrierRuinTime X a ω)
    (hNext : ε < X.X (u + T) ω - X.X u ω)
    (hPost : ∀ t : ℝ≥0, t ≤ T →
      sSup ((fun r : ℝ≥0 => X.X (u + r) ω) '' Set.Icc 0 t) -
        X.X (u + t) ω ≤ a) :
    twoSidedExitUpTime X (b + ε) ω < barrierRuinTime X a ω := by sorry
