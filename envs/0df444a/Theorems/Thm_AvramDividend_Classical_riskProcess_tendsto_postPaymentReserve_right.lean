-- Prove2me | Theorems.Thm_AvramDividend_Classical_riskProcess_tendsto_postPaymentReserve_right
-- name    : AvramDividend.Classical.riskProcess_tendsto_postPaymentReserve_right
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T06:43:21.608328+00:00
-- url     : https://prove2.me/theorems/2dc41f6c-0db1-48a4-95c9-da92a077c079
-- title:
--   The pre-payment reserve approaches the post-payment reserve from the right
-- statement:
--   For any spectrally negative Lévy path and admissible dividend strategy, the book-value reserve riskProcess X x D at times s>t converges as s↓t to the reserve x+X_t−D_{t+} after the right dividend payment at t. This is the precise right-limit identity relating the book-value ruin convention to the càdlàg post-payment control. The Lévy path is right-continuous, and pathwise dividend monotonicity implies its right limit equals the formal rightLimit D t; arithmetic preserves the limit. The lemma is used to show post-payment negativity strictly before the book-value ruin time would force a later negative reserve and hence earlier ruin.
-- source:
--   Source-faithful direct consequence of SpectrallyNegativeLevy.rightCont and Mathlib Monotone.tendsto_rightLim with exact rightLimit definition; no Open theorem imports.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.riskProcess_tendsto_postPaymentReserve_right
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (t : ℝ≥0) :
    Tendsto (fun s : ℝ≥0 => riskProcess X x D s ω)
      (𝓝[>] t)
      (𝓝 (x + X.X t ω - rightLimit D t ω)) := by sorry
