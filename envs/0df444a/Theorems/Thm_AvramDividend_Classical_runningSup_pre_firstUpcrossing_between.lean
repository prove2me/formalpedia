-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_pre_firstUpcrossing_between
-- name    : AvramDividend.Classical.runningSup_pre_firstUpcrossing_between
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T06:13:23.928147+00:00
-- url     : https://prove2.me/theorems/56115070-7c5f-4e27-8208-7ea9a35f0e36
-- title:
--   Running supremum remains between zero and the passage threshold before first upcrossing
-- statement:
--   For a spectrally negative Lévy path, let u be its first strict upward passage time over the level b, assumed finite and represented as a nonnegative real. At every time t strictly before u, the running supremum is nonnegative and no larger than b. This is the exact running-peak bound needed to specialise the independently proved drawdown exit-event and first-hitting-time sandwiches to the actual first-upcrossing prefix, without assuming strong Markov or the two-sided exit scale formula.
-- source:
--   Avram Palmowski Pistorius (2007), Proposition 1 killed-reflected path comparison. Derived from already-Proved Prove2Me lemmas firstUpcrossing_prethreshold_le (ca03b30a-8ef0-4424-b880-caf139df13fe) and runningSup_eq_rawSup_nonneg (992246e6-0bba-4d6f-bd75-5b29c32037f9).

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_prethreshold_le
import Theorems.Thm_AvramDividend_Classical_runningSup_eq_rawSup_nonneg

open MeasureTheory
open AvramDividend.Classical
open Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.runningSup_pre_firstUpcrossing_between
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (b : ℝ) (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : b < X.X s ω), (s : ℝ≥0∞))) :
    ∀ t : ℝ≥0, t < u →
      0 ≤ runningSup X t ω ∧ runningSup X t ω ≤ b := by sorry
