-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_locmoll_band_atomic_cash_summable
-- name    : AvramDividend.Classical.avram_locmoll_band_atomic_cash_summable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:24:46.649145+00:00
-- url     : https://prove2.me/theorems/6d0c79fd-0f08-44b7-a1ef-fd226ec07af2
-- title:
--   All eligible discounted right-payment masses are summable over physical times
-- statement:
--   All eligible discounted right-payment masses are summable over physical times
-- source:
--   Exact dividend convergence reduction of 5d5b4160-dbec-53b8-b2ad-8979f199b2d3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_locmoll_band_atomic_cash_summable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ) (hq : 0 ≤ q)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (θ : ℝ≥0) :
    Summable (fun s : ℝ≥0 =>
      if s ≤ θ ∧ (s = 0 ∨ (s : ℝ≥0∞) < ruinTime X x D ω) then
        Real.exp (-(q * (s : ℝ))) * (rightLimit D s ω - D s ω)
      else 0) := by sorry
