-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_future_increment_indep_rightCont_prior
-- name    : AvramDividend.Classical.levy_future_increment_indep_rightCont_prior
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T17:14:40.701926+00:00
-- url     : https://prove2.me/theorems/e1e2f3ca-1ff9-4c58-9bd8-3117ae49e567
-- title:
--   Future Lévy increments are independent of an earlier right-continuous filtration
-- statement:
--   For nonnegative times s<u≤t, a published spectrally negative Lévy process has X_t minus X_u independent of the enlarged right-continuous past F_{s+}. This follows from the exact pinned identity F_{s+}=inf over all v>s of F_v and original independence of the increment from F_u. It gives an unconditional building block for passage u down to s, which still requires a separate limit theorem.
-- source:
--   Pinned Mathlib Filtration.rightCont_eq and indep_of_indep_of_le_right; published Prove2Me SpectrallyNegativeLevy.indepIncrements.

import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Independence.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_future_increment_indep_rightCont_prior
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s u t : ℝ≥0) (hsu : s < u) (hut : u ≤ t) :
    Indep
      (MeasurableSpace.comap (fun ω => X.X t ω - X.X u ω) inferInstance)
      (𝓕.rightCont s) P := by sorry
