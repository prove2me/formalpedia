-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_locmoll_band_cash_coverage
-- name    : AvramDividend.Classical.avram_locmoll_band_cash_coverage
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T22:02:08.680893+00:00
-- url     : https://prove2.me/theorems/7b08f067-0b33-40c4-b915-c8a0beeebb77
-- title:
--   Every eligible pre-ruin payment is eventually covered by nested strict-band clocks
-- statement:
--   Every eligible pre-ruin payment is eventually covered by nested strict-band clocks
-- source:
--   Exact decomposition of 1956f1aa-dda2-5052-8723-910f7fb63181, Avram Proposition 4(i)

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_locmoll_band_cash_coverage
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (T : ℝ) (hT : 0 ≤ T) (δ R : ℕ → ℝ)
    (hd : Tendsto δ atTop (𝓝 0)) (hR : Tendsto R atTop atTop)
    (θ : ℕ → Ω → ℝ≥0)
    (hcover : ∀ k ω t, t ≤ T.toNNReal →
      (∀ s : ℝ≥0, s ≤ t → x + X.X s ω - rightLimit D s ω ∈ Icc (δ k) (R k)) →
      t ≤ θ k ω)
    (hpos : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ T.toNNReal →
      (t : ℝ≥0∞) < ruinTime X x D ω → 0 < x + X.X t ω - rightLimit D t ω) :
    ∀ᵐ ω ∂P, ∀ t ∈ paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ∃ k, t ≤ (θ k ω : ℝ) := by sorry
