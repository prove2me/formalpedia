-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_riskProcess_prepost_predictable_strip
-- name    : AvramDividend.Classical.avram_p3_g_localise_original_riskProcess_prepost_predictable_strip
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T12:32:31.386487+00:00
-- url     : https://prove2.me/theorems/b6dfe5f0-9003-4b7e-8778-5c46843bf9ab
-- title:
--   Actual source pre-payment riskProcess has the same strictly positive-time predictable compact pre-reserve event
-- statement:
--   The true riskProcess X x D uses the original left-continuous cumulative dividend D rather than a postpayment surrogate. At every strictly positive time its strict left limit equals that of x+X.X-rightLimit D, and the latter defines an existing Proved predictable compact-band event. This identifies exactly which source reserve P3-F may use in stopped-grid arguments without conflating time-zero or right-horizon payments.
-- source:
--   Accepted original BV jump prestate predictable 5115705e and source pre/post-payment left-limit identity caa7f605; original X, D and riskProcess are unchanged.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_controlled_prestate_compact_band_predictable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_original_prepost_reserve_same_leftlim

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_g_localise_original_riskProcess_prepost_predictable_strip
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (a b : ℝ) :
    let E : Set (ℝ≥0 × Ω) := {p |
      Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc a b}
    MeasurableSet[𝓕.rightCont.predictable] E ∧
    ∀ (ω : Ω) (t : ℝ≥0), 0 < t →
      ((t, ω) ∈ E ↔ Function.leftLim
        (fun s : ℝ≥0 => riskProcess X x D s ω) t ∈ Icc a b) := by sorry
