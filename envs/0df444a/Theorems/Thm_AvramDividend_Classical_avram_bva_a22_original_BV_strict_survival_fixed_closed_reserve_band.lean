-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_BV_strict_survival_fixed_closed_reserve_band
-- name    : AvramDividend.Classical.avram_bva_a22_original_BV_strict_survival_fixed_closed_reserve_band
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T07:21:32.592732+00:00
-- url     : https://prove2.me/theorems/9e9c9e74-dbae-4c03-bb11-b4b51b099837
-- title:
--   Original bounded-variation strictly surviving controlled postpayment reserves inhabit one fixed closed nonnegative horizon band
-- statement:
--   Under the genuine original BV spectrally negative Levy process with nonnegative physical drift and admissible original dividend control, every pre-ruin controlled post-rightpayment reserve, including the origin, within a fixed horizon T belongs almost surely to the same deterministic closed interval [0, x+T drift]. The lower bound comes from original admissibility, the upper bound from the original no-positive-jump BV drift envelope. This provides the uniform closed-band endpoint inclusion needed to apply the zero-reserve terminal one-sided continuity modulus on the strict-survival branch of BVA96. For negative physical drift a separate branch must be treated.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_preruin_postpayment_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_postpayment_deterministic_horizon_upper_strip
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva_a22_original_BV_strict_survival_fixed_closed_reserve_band
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hDs : IsDividendStrategy 𝓕 D)
    (T : ℝ≥0) (hd : 0 ≤ X.drift) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ T →
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      (x + X.X t ω - rightLimit D t ω) ∈
        Icc (0 : ℝ) (x + (T : ℝ) * X.drift) := by sorry
