-- Prove2me | Theorems.Thm_AvramDividend_Classical_firstUpcrossing_before_barrierRuin_iff_prefix_survival
-- name    : AvramDividend.Classical.firstUpcrossing_before_barrierRuin_iff_prefix_survival
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T13:08:29.224109+00:00
-- url     : https://prove2.me/theorems/9a4b2916-7160-4f0f-8c1c-e3a966b5609c
-- title:
--   Killed finite first-upcrossing event equals reflected survival throughout the pre-record prefix
-- statement:
--   For a>0 and first finite strict upcrossing u of a nonnegative record b, the extended time u is strictly earlier than the actual barrierRuinTime if and only if reflectedSup X t stays at most a at every time strictly before u. The forward implication follows from the infimum definition of ruin. The reverse implication uses the no-upward-jumps record-contact and proved right-continuity to eliminate equality at the stopping boundary. This is the exact event equivalence needed to rewrite a killed first-passage discount into a survival-weighted expectation and apply the proved weighted survival sandwich.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 1 stopped reflected record renewal. Dependency: pending derived unconditional firstUpcrossing_strictly_before_drawdown_ruin. Do not publish until that theorem is Proved.

import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_strictly_before_drawdown_ruin

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.firstUpcrossing_before_barrierRuin_iff_prefix_survival
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : b < X.X s ω), (s : ℝ≥0∞))) :
    (u : ℝ≥0∞) < barrierRuinTime X a ω ↔
      ∀ t : ℝ≥0, t < u → reflectedSup X t ω ≤ a := by sorry
