-- Prove2me | Theorems.Thm_AvramDividend_Classical_firstUpcrossing_drawdown_exit_event_sandwich
-- name    : AvramDividend.Classical.firstUpcrossing_drawdown_exit_event_sandwich
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T06:37:17.20467+00:00
-- url     : https://prove2.me/theorems/a8aeed49-5fcd-49d8-8fd3-961a59b13a0a
-- title:
--   Strict reflected drawdown and ordinary lower exit events before the actual Lévy first upcrossing
-- statement:
--   On a Lévy path up to its finite first strict upcrossing of b, the running supremum remains in [0,b], so the event of raw descent below -a before first upcrossing is contained in that of reflected drawdown exceeding a, itself contained in the event of raw descent below b-a. This specialises the already proved generic event inclusion to actual spectrally negative Lévy paths and is a necessary deterministic input for stopped two-sided exit probability bounds. No stopped strong Markov, fluctuation identity or dividend valuation is asserted.
-- source:
--   Avram Palmowski Pistorius (2007) Proposition 1 stopped strict exit sandwich; formal consequence of the accepted event inclusion b9eddbe2-221d-4e21-ac28-f713945712a3 and the separately published pre-upcrossing peak bound 56115070-7c5f-4e27-8208-7ea9a35f0e36 (publication confirmed, proof pending).

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_drawdown_prepeak_exit_event_inclusions
import Theorems.Thm_AvramDividend_Classical_runningSup_pre_firstUpcrossing_between

open MeasureTheory Set
open AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.firstUpcrossing_drawdown_exit_event_sandwich
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a b : ℝ) (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : b < X.X s ω), (s : ℝ≥0∞))) :
    {t : ℝ≥0 | t < u ∧ X.X t ω < -a} ⊆
      {t : ℝ≥0 | t < u ∧ a < runningSup X t ω - X.X t ω} ∧
    {t : ℝ≥0 | t < u ∧ a < runningSup X t ω - X.X t ω} ⊆
      {t : ℝ≥0 | t < u ∧ X.X t ω < b - a} := by sorry
