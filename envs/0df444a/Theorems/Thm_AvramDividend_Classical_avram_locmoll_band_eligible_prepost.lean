-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_locmoll_band_eligible_prepost
-- name    : AvramDividend.Classical.avram_locmoll_band_eligible_prepost
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:24:44.153812+00:00
-- url     : https://prove2.me/theorems/0fa8d4d3-e7dd-522e-902e-b31af9dd675a
-- title:
--   Eligible prepayment and postpayment reserves lie in the same compact interval
-- statement:
--   Eligible prepayment and postpayment reserves lie in the same compact interval
-- source:
--   Exact dividend convergence reduction of 5d5b4160-dbec-53b8-b2ad-8979f199b2d3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_locmoll_band_eligible_prepost
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (δ R : ℝ) (hxR : x < R) (θ : Ω → ℝ≥0)
    (hprefix : ∀ ω t, t < θ ω →
      x + X.X t ω - rightLimit D t ω ∈ Icc δ R) :
    ∀ ω s, s ≤ θ ω →
      (s = 0 ∨ (s : ℝ≥0∞) < ruinTime X x D ω) →
      riskProcess X x D s ω ∈ Icc 0 R ∧
        x + X.X s ω - rightLimit D s ω ∈ Icc 0 R := by sorry
