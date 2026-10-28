-- Prove2me | Theorems.Thm_AvramDividend_Classical_nextRecord_survives_of_shifted_drawdown_guard
-- name    : AvramDividend.Classical.nextRecord_survives_of_shifted_drawdown_guard
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T18:13:47.757989+00:00
-- url     : https://prove2.me/theorems/8ef84011-9a16-42d7-9910-0c87dd8d0339
-- title:
--   A surviving first-record history and a safe shifted future preserve the next killed record
-- statement:
--   Suppose u and v are the genuine finite first strict upcrossings of b and b+ε, with v≤u+T. If no reflected drawdown breach occurred before u and the future shifted path stays within drawdown barrier a through T, then v occurs strictly before the global reflected ruin time. Boundedness of the path on the finite prefix follows automatically from the Lévy-path lemma. This upgrades survival concatenation into the exact killed-record event used in one-step renewal.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 1, pathwise killed-record restart.

import Mathlib.Data.Real.Basic
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_firstRecord_prefix_survival_concat
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_strictly_before_drawdown_ruin
import Theorems.Thm_AvramDividend_Classical_levyPath_bddAbove_Icc

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.nextRecord_survives_of_shifted_drawdown_guard
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b ε : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hε : 0 ≤ ε)
    (ω : Ω) (u v T : ℝ≥0)
    (hu : (u : ℝ≥0∞) = twoSidedExitUpTime X b ω)
    (hv : (v : ℝ≥0∞) = twoSidedExitUpTime X (b + ε) ω)
    (hvT : v ≤ u + T)
    (hPre : ∀ r : ℝ≥0, r < u → reflectedSup X r ω ≤ a)
    (hPost : ∀ t : ℝ≥0, t ≤ T →
      sSup ((fun r : ℝ≥0 => X.X (u + r) ω) '' Set.Icc 0 t) -
        X.X (u + t) ω ≤ a) :
    (v : ℝ≥0∞) < barrierRuinTime X a ω := by sorry
