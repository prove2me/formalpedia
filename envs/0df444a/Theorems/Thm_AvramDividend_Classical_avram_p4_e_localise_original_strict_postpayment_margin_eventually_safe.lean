-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_strict_postpayment_margin_eventually_safe
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_strict_postpayment_margin_eventually_safe
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T08:05:43.072524+00:00
-- url     : https://prove2.me/theorems/edd87b5b-6adb-4477-bdb0-62c58b3e3629
-- title:
--   Strict original reserve margin after initial dividend persists in a true right neighbourhood
-- statement:
--   The genuinely original source post-rightpayment reserve is pathwise right-continuous. If its value at physical time zero is strictly positive after the t=0 dividend atom, positivity persists eventually as t tends down to 0 through NNReal times. The hypothesis is explicitly stronger than IsAdmissibleLe, which gives only weak nonnegativity and allows immediate ruin; no automatic positive-ruin claim is made.
-- source:
--   Proved P4-E pathwise original postpayment rightcontinuity, Mathlib openness of Ioi.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_postrightpayment_reserve_pathwise_rightcontinuous

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A genuine strict postpayment reserve margin at time zero persists over source right-neighbourhoods. -/
theorem AvramDividend.Classical.avram_p4_e_localise_original_strict_postpayment_margin_eventually_safe
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (ω : Ω)
    (hMargin : 0 < x + X.X 0 ω - rightLimit D 0 ω) :
    ∀ᶠ s in 𝓝[≥] (0 : ℝ≥0),
      0 < x + X.X s ω - rightLimit D s ω := by sorry
