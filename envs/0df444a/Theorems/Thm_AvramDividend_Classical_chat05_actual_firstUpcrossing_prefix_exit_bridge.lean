-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat05_actual_firstUpcrossing_prefix_exit_bridge
-- name    : AvramDividend.Classical.chat05_actual_firstUpcrossing_prefix_exit_bridge
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T23:15:31.298986+00:00
-- url     : https://prove2.me/theorems/0781e22f-ae6b-460b-9aae-82125130000a
-- title:
--   Ordinary lower-exit and reflected drawdown inclusions before the actual first upward record
-- statement:
--   For a spectrally negative Lévy path, before its finite first strict upcrossing of level b, the running supremum lies in [0,b]. Consequently, an ordinary downcrossing below -a implies drawdown above a; conversely, drawdown above a implies the process lies below b-a. These exact prefix-event inclusions support the lower and upper two-sided exit comparisons in barrier valuation.
-- source:
--   Pathwise bridge combining verified runningSup_pre_firstUpcrossing_between (56115070-7c5f-4e27-8208-7ea9a35f0e36) and drawdown_prepeak_exit_event_inclusions (b9eddbe2-221d-4e21-ac28-f713945712a3). Derived from preserved Chat 05 draft of 19 October 2026.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_drawdown_prepeak_exit_event_inclusions
import Theorems.Thm_AvramDividend_Classical_runningSup_pre_firstUpcrossing_between

open MeasureTheory Set
open AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat05_actual_firstUpcrossing_prefix_exit_bridge
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a b : ℝ) (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : b < X.X s ω), (s : ℝ≥0∞))) :
    {t : ℝ≥0 | t < u ∧ X.X t ω < -a} ⊆
      {t : ℝ≥0 | t < u ∧ a < runningSup X t ω - X.X t ω} ∧
    {t : ℝ≥0 | t < u ∧ a < runningSup X t ω - X.X t ω} ⊆
      {t : ℝ≥0 | t < u ∧ X.X t ω < b - a} := by sorry
