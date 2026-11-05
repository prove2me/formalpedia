-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_leanlevy_bridge_original_finite_band_rate_square_ennreal
-- name    : AvramDividend.Classical.avram_leanlevy_bridge_original_finite_band_rate_square_ennreal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T16:22:15.191906+00:00
-- url     : https://prove2.me/theorems/35bbaf6a-c0b7-4c81-8716-fd3cf692f602
-- title:
--   Finite original negative-band Lévy rate squared converts exactly to ENNReal
-- statement:
--   For the actual Lévy measure ν_X on the original probability space and the negative cutoff band B, the finite intensity condition identifies the lifted real quadratic half-rate with the ENNReal square of the genuine horizon-intensity product. This is the missing codomain adapter for passing the physical P2-E grid-pair expectation limit into P4-F's exact chronological factorial moment. The theorem assumes source ν_X B finite, available from the Proved original rate finiteness helper 86086cb2.
-- source:
--   Pinned Mathlib ENNReal.ofReal_div_of_pos, ENNReal.ofReal_pow, ENNReal.ofReal_mul, ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_toReal with ν finite; original-source P2-A negative Borel band finiteness 86086cb2.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_leanlevy_bridge_original_finite_band_rate_square_ennreal
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ)
    (hν : X.ν (Iic (-(1 / ((n : ℝ) + 1)))) < ⊤) :
    ENNReal.ofReal
      ((((T : ℝ) *
        (X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal) ^ 2) / 2) =
      (((T : ℝ≥0∞) *
        X.ν (Iic (-(1 / ((n : ℝ) + 1))))) ^ 2) / 2 := by sorry
