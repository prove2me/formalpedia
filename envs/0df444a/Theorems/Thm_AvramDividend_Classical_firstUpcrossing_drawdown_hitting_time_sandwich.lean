-- Prove2me | Theorems.Thm_AvramDividend_Classical_firstUpcrossing_drawdown_hitting_time_sandwich
-- name    : AvramDividend.Classical.firstUpcrossing_drawdown_hitting_time_sandwich
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T10:09:41.551568+00:00
-- url     : https://prove2.me/theorems/914a8be3-950c-48d0-b3be-42e7168401a2
-- title:
--   First passage below the two raw thresholds brackets drawdown ruin before a finite Lévy upcrossing
-- statement:
--   On a Lévy sample path before its finite first strict upcrossing time u of level b, the running supremum lies between 0 and b. Consequently the first raw downward exit below b−a occurs no later than the first drawdown excursion strictly above a, and that occurs no later than the first raw downward exit below −a, with all three time infima restricted to times t<u and valued in ℝ≥0∞. This is a deterministic pathwise first-hitting-time comparison. It does not prove the discounted scale-function exit probability or Markov property.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 1, first passage / drawdown comparison; formal specialisation of two Prove2Me proved lemmas f8268b67-22a3-4de5-9a84-0a41e3408f8e and 56115070-7c5f-4e27-8208-7ea9a35f0e36.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_prepeak_reflected_ruin_hitting_time_sandwich
import Theorems.Thm_AvramDividend_Classical_runningSup_pre_firstUpcrossing_between

open MeasureTheory Set
open AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.firstUpcrossing_drawdown_hitting_time_sandwich
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a b : ℝ) (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : b < X.X s ω), (s : ℝ≥0∞))) :
    sInf (Set.image (fun t : ℝ≥0 => (t : ℝ≥0∞))
      {t : ℝ≥0 | t < u ∧ X.X t ω < b - a}) ≤
    sInf (Set.image (fun t : ℝ≥0 => (t : ℝ≥0∞))
      {t : ℝ≥0 | t < u ∧ a < runningSup X t ω - X.X t ω}) ∧
    sInf (Set.image (fun t : ℝ≥0 => (t : ℝ≥0∞))
      {t : ℝ≥0 | t < u ∧ a < runningSup X t ω - X.X t ω}) ≤
    sInf (Set.image (fun t : ℝ≥0 => (t : ℝ≥0∞))
      {t : ℝ≥0 | t < u ∧ X.X t ω < -a}) := by sorry
