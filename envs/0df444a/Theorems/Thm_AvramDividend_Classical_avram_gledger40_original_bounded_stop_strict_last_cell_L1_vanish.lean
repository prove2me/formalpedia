-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger40_original_bounded_stop_strict_last_cell_L1_vanish
-- name    : AvramDividend.Classical.avram_gledger40_original_bounded_stop_strict_last_cell_L1_vanish
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T19:40:01.399265+00:00
-- url     : https://prove2.me/theorems/ef3e9cd7-fe0b-4a3b-8ee6-562cc4e21a80
-- title:
--   Original bounded stopping-clock strict last-cell discounted cash expectation vanishes
-- statement:
--   For an original dividend measure and a bounded right-continuous filtration stopping clock, the expected discounted pre-clock dividend cash in the open last physical mesh cell tends to zero. The cell interval is open at the clock, excluding its right-payment atom. Specialise the proved random strict contact tail and uniform-mesh antitone convergence; no Gaussian auxiliary process is introduced.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_gledger40_original_bounded_stop_strict_last_cell_L1_vanish
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q) (n : ℕ) (hn : 0 < n)
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρbound : ∀ ω, ρ ω ≤ (n : ℝ≥0)) :
    Tendsto (fun m : ℕ =>
      ∫ ω : Ω, (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
          Ioo ((ρ ω : ℝ) - (n : ℝ) / ((m : ℝ) + 2)) (ρ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal ∂P)
      atTop (𝓝 (0 : ℝ)) := by sorry
