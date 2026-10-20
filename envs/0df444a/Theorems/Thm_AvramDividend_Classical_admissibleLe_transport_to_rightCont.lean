-- Prove2me | Theorems.Thm_AvramDividend_Classical_admissibleLe_transport_to_rightCont
-- name    : AvramDividend.Classical.admissibleLe_transport_to_rightCont
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T19:20:31.657909+00:00
-- url     : https://prove2.me/theorems/e8cf033a-c794-4b82-ba77-07f03860d70b
-- title:
--   A capped dividend control remains admissible after right-continuation of filtration
-- statement:
--   Suppose X is the original spectrally negative Lévy process, Y is any such Lévy process on the right-continuous filtration, and Y.X = X.X pathwise. Then every strategy D admissible for X with cap C and initial capital x is also admissible for Y with the same cap. The original control's adaptedness transfers by the already proved dividendStrategy_rightCont_filtration theorem. The controlled risk process and ruin time agree because Y.X=X.X. Consequently the dividend jump solvency inequalities and cap constraint are preserved exactly. This provides the controlled-strategy transport required to use stochastic verification under right-continuation, without depending on the as-yet-unproved complete process-reconstruction theorem.
-- source:
--   Pinned Formalpedia IsAdmissibleLe, riskProcess, ruinTime and proved AvramDividend.Classical.dividendStrategy_rightCont_filtration.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightCont_filtration

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.admissibleLe_transport_to_rightCont
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (Y : SpectrallyNegativeLevy P 𝓕.rightCont)
    (hXY : Y.X = X.X)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D) :
    IsAdmissibleLe Y x C D := by sorry
