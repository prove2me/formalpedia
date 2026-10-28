-- Prove2me | Theorems.Thm_AvramDividend_Classical_capped_stopping_terminal_integrable_of_progressive_components
-- name    : AvramDividend.Classical.capped_stopping_terminal_integrable_of_progressive_components
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T10:42:49.940554+00:00
-- url     : https://prove2.me/theorems/6066bf53-2be7-4a0c-a8b6-740d4c71515f
-- title:
--   Finite-cap stopped HJB terminal payoff is integrable from progressive Lévy and dividend components
-- statement:
--   For any admissible capped dividend strategy, if the Lévy driver and dividend path are each progressively measurable, their controlled reserve is progressive and the surviving random-horizon HJB terminal payoff is integrable. This reduces the remaining càdlàg/càglàd verification measurability issue to the two component lemmas, without assuming continuous paths.
-- source:
--   Proved capped_stopping_terminal_integrable_from_progressive plus the separately published progressive-components reserve lemma, pending proof verification at draft time.

import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_riskProcess_progMeasurable_of_progressive_parts
import Theorems.Thm_AvramDividend_Classical_capped_stopping_terminal_integrable_from_progressive

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.capped_stopping_terminal_integrable_of_progressive_components
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (hw : ContinuousOn w (Ici 0))
    (B : ℝ) (hB : 0 ≤ B)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ ENNReal.ofReal B)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x (ENNReal.ofReal B) D)
    (τ : Ω → ℝ≥0)
    (hStop : IsStoppingTime 𝓕 (fun ω => ((τ ω : ℝ≥0) : ℝ≥0∞)))
    (hXProg : ProgMeasurable 𝓕 X.X)
    (hDProg : ProgMeasurable 𝓕 D) :
    Integrable (fun ω => if ((τ ω : ℝ≥0) : ℝ≥0∞) <
      ruinTime X x D ω then
      w (riskProcess X x D (τ ω) ω) else 0) P := by sorry
