-- Prove2me | Theorems.Thm_AvramDividend_Classical_survived_nextRecord_strict_shifted_exit_with_minimal_imports
-- name    : AvramDividend.Classical.survived_nextRecord_strict_shifted_exit_with_minimal_imports
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T22:47:54.66567+00:00
-- url     : https://prove2.me/theorems/78395573-c5ec-4d81-98e5-ff775a38dcab
-- title:
--   A surviving higher Lévy record strictly precedes shifted lower exit
-- statement:
--   For every spectrally negative Lévy path with a finite first record and a finite higher record that survives reflected drawdown ruin, the shifted strict upward passage from the first record occurs strictly before shifted strict lower passage at -a. Right-continuity comes automatically from the proved Lévy shifted-increments lemma, so no extra path regularity premise remains. This is the pathwise upper-event inclusion required for the geometric stopped-renewal estimate.
-- source:
--   Apply the strict shifted exit-order theorem and supply the proven automatic right continuity of shifted Lévy increments.

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_survived_nextRecord_shifted_upclock_le_lower_exit

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.survived_nextRecord_strict_shifted_exit_with_minimal_imports
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (a b ε : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hε : 0 ≤ ε)
    (u v δ : ℝ≥0)
    (hu : (u : ℝ≥0∞) = twoSidedExitUpTime X b ω)
    (hAt : X.X u ω = b)
    (hv : (v : ℝ≥0∞) = twoSidedExitUpTime X (b + ε) ω)
    (hδ : u + δ = v)
    (hSurvive : (v : ℝ≥0∞) < barrierRuinTime X a ω) :
    (⨅ (t : ℝ≥0)
        (_ : ε < X.X (u + t) ω - X.X u ω), (t : ℝ≥0∞)) <
    (⨅ (t : ℝ≥0)
        (_ : X.X (u + t) ω - X.X u ω < -a), (t : ℝ≥0∞)) := by sorry
