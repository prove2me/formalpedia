-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_allnu_unadjusted_source_iff_no_right_dividend_atom
-- name    : AvramDividend.Classical.avram_p4_f3_original_allnu_unadjusted_source_iff_no_right_dividend_atom
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T23:26:51.665203+00:00
-- url     : https://prove2.me/theorems/b44048fe-4852-4a6b-bab4-122484d714e1
-- title:
--   Original all-ν unadjusted postpayment source identity iff right dividend atom is zero
-- statement:
--   Under a same-space decomposition of the actual original spectrally negative Lévy process, the unadjusted identity equating pre-right-payment riskProcess and postpayment source is valid at a sample/time exactly when the dividend right atom vanishes. The equivalence is necessary and sufficient and handles arbitrary Lévy jumps; it identifies the exact missing hypothesis of the Open 653fe960 target.
-- source:
--   Original riskProcess definition and source split; iff reduced to equality of D t and rightLimit D t by real linear algebra.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f3_original_allnu_unadjusted_source_iff_no_right_dividend_atom
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (Y : SpectrallyNegativeLevy P 𝓕)
    (hYν : Y.ν = 0) (hYσ : Y.σ = X.σ)
    (Jsmall Jlarge : ℝ≥0 → Ω → ℝ)
    (hSourceDecomp : ∀ (u : ℝ≥0) (η : Ω),
      X.X u η = (u : ℝ) * X.c +
        (Y.X u η - (u : ℝ) * Y.c) + Jsmall u η + Jlarge u η)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (t : ℝ≥0) (ω : Ω) :
    (riskProcess X x D t ω =
      x + ((t : ℝ) * X.c +
        (Y.X t ω - (t : ℝ) * Y.c) +
          Jsmall t ω + Jlarge t ω) - rightLimit D t ω) ↔
      rightLimit D t ω = D t ω := by sorry
