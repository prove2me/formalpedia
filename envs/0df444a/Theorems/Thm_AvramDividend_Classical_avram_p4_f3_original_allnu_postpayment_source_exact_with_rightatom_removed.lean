-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_allnu_postpayment_source_exact_with_rightatom_removed
-- name    : AvramDividend.Classical.avram_p4_f3_original_allnu_postpayment_source_exact_with_rightatom_removed
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T23:22:29.967486+00:00
-- url     : https://prove2.me/theorems/7c2bb566-0911-46af-a748-5a0ded1518da
-- title:
--   Original all-ν postpayment source identity after subtracting the right dividend atom
-- statement:
--   The original controlled riskProcess is pre-right-dividend. Subtracting the exact dividend right atom gives the postpayment reserve. With an assumed original same-space Gaussian/jump split, this equals the decomposed source minus rightLimit D, at all physical sample times including t=0. This corrects the false unadjusted original source identity 653fe960 while preserving original Lévy paths.
-- source:
--   Original source riskProcess definition and source decomposition, with exact dividend right atom algebra.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f3_original_allnu_postpayment_source_exact_with_rightatom_removed
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
    riskProcess X x D t ω -
      (rightLimit D t ω - D t ω) =
      x + ((t : ℝ) * X.c +
        (Y.X t ω - (t : ℝ) * Y.c) +
          Jsmall t ω + Jlarge t ω) - rightLimit D t ω := by sorry
