-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat08_deterministic_levy_increment_regeneration
-- name    : AvramDividend.Classical.chat08_deterministic_levy_increment_regeneration
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T08:37:46.607412+00:00
-- url     : https://prove2.me/theorems/4a1dc17e-40bf-46c2-acad-ef625e69bedd
-- title:
--   Deterministic Lévy increment regeneration from stationary independent increments
-- statement:
--   At every deterministic time s and future offset u, the increment X(s+u)-X(s) has the same law as X(u) and is independent of information in the past filtration at s.
-- source:
--   SpectrallyNegativeLevy.stationaryIncrements and SpectrallyNegativeLevy.indepIncrements.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat08_deterministic_levy_increment_regeneration
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) (s u : ℝ≥0) :
    IdentDistrib
        (fun ω => X.X (s + u) ω - X.X s ω) (X.X u) P P ∧
      Indep
        (MeasurableSpace.comap
          (fun ω => X.X (s + u) ω - X.X s ω) inferInstance)
        (ℱ s) P := by sorry
