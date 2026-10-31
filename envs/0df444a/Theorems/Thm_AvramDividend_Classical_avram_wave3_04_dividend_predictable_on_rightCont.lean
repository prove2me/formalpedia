-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_04_dividend_predictable_on_rightCont
-- name    : AvramDividend.Classical.avram_wave3_04_dividend_predictable_on_rightCont
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:44:54.35197+00:00
-- url     : https://prove2.me/theorems/a8ce44bc-4e9b-4076-85ab-864d3ce7ba72
-- title:
--   The original dividend strategy remains predictable after right-continuous filtration transport
-- statement:
--   For any filtration and any adapted, nondecreasing, left-continuous cumulative dividend control, the original payment process is measurable with respect to the predictable sigma-algebra of the filtration’s right-continuous enlargement:
--
--   $$D:(t,\omega)\mapsto D_t(\omega)\quad\text{is }\mathcal P(\mathcal F_{t+})\text{-measurable}.$$
--
--   This is the actual original source control, including diffuse and right-atomic Stieltjes payments. Right-continuous filtration transport is independently proved to preserve its dividend-strategy properties, so the result supplies the predictable control input in the same enlarged filtration used for the original Lévy reconstruction.
-- source:
--   Avram–Palmowski–Pistorius (2007), Proposition 4(i), original adapted left-continuous dividend strategies: https://avram.perso.univ-pau.fr/papers/Martijn/dividend.pdf. Formal dependencies are the Proved dividendStrategy_rightCont_filtration (bd2bcc87-3afa-47ef-bdbe-48e8f4379c0c) and the Proved avram_wave3_04_dividend_strategy_predictable (a4ef06a5-5b73-4d29-8e89-4a60aa82c3c5).

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_dividend_strategy_predictable

open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_04_dividend_predictable_on_rightCont
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) :
    @Measurable (ℝ≥0 × Ω) ℝ 𝓕.rightCont.predictable inferInstance
      (fun p => D p.1 p.2) := by sorry
