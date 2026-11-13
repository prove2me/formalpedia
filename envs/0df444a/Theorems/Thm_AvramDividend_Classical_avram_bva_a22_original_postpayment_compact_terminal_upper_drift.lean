-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_postpayment_compact_terminal_upper_drift
-- name    : AvramDividend.Classical.avram_bva_a22_original_postpayment_compact_terminal_upper_drift
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T00:10:03.285177+00:00
-- url     : https://prove2.me/theorems/f4154147-1652-4021-9176-42ff72b520ce
-- title:
--   Original BV controlled reserve C1 compact terminal positive increase bounded by Lévy drift and horizon length
-- statement:
--   On the original spectrally negative bounded-variation Lévy process and actual admissible dividend strategy (as IsDividendStrategy), prove a source-exact pathwise upper bound on the increase in a candidate value w over every pair of ordered physical times. When both original post-rightpayment controlled reserve endpoints lie in a fixed strict compact reserve interval and w obeys the natural compact one-sided Lipschitz bound, the positive change is at most L times elapsed time times the positive part of the original physical Lévy drift. This follows by the Proved original controlled-reserve increment envelope and positivity of the elapsed time. It captures the omitted horizon strip from uniform physical grids, with no independent process, finite activity or generator global L1.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_controlled_postpayment_increment_drift_envelope
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva_a22_original_postpayment_compact_terminal_upper_drift
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (c d L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ y ∈ Icc c d, ∀ z ∈ Icc c d,
      w z - w y ≤ L * max (z - y) 0) :
    ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, s ≤ t →
      (x + X.X s ω - rightLimit D s ω) ∈ Icc c d →
      (x + X.X t ω - rightLimit D t ω) ∈ Icc c d →
      w (x + X.X t ω - rightLimit D t ω) -
        w (x + X.X s ω - rightLimit D s ω) ≤
      L * (((t : ℝ) - (s : ℝ)) * max X.drift 0) := by sorry
