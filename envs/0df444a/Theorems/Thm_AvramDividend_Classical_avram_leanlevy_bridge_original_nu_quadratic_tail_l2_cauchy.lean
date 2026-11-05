-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_leanlevy_bridge_original_nu_quadratic_tail_l2_cauchy
-- name    : AvramDividend.Classical.avram_leanlevy_bridge_original_nu_quadratic_tail_l2_cauchy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T13:29:26.677612+00:00
-- url     : https://prove2.me/theorems/42d4b2ac-8114-433e-80a0-375f2bec6c74
-- title:
--   Original Levy quadratic ν-tail yields uniform finite-band L2 Cauchy under physical square-energy estimate
-- statement:
--   On Avram's unchanged probability space and right-continuous filtration, use the Proved intrinsic Lévy-measure small-negative-jump quadratic-tail limit to turn any physically established L2 band-distance bound proportional to the square root of that tail into a Cauchy family. Requires finite real quadratic tails and an explicit original stopped-band L2 distance bound; does not assume or construct a synthetic Poisson representation.
-- source:
--   Proved source quadratic-tail theorem e5cc5d15 and Proved original L2 band Cauchy criterion d3a30c29, bridged through ENNReal.tendsto_toReal_zero_iff and continuity of Real.sqrt/multiplication.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_nu_quadratic_tail_tendsto_zero
import Theorems.Thm_AvramDividend_Classical_avram_leanlevy_bridge_original_l2_cauchy_of_uniform_band_tail
open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_leanlevy_bridge_original_nu_quadratic_tail_l2_cauchy
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (M : ℕ → ℝ≥0 → Lp ℝ (2 : ℝ≥0∞) P)
    (C : ℝ)
    (hFinite : ∀ n : ℕ, (∫⁻ z in Ioc (-(1 / ((n : ℝ) + 1))) (0 : ℝ),
        ENNReal.ofReal (z ^ 2) ∂X.ν) ≠ ⊤)
    (hBandBound : ∀ t n m, n ≤ m →
      dist (M n t) (M m t) ≤
        C * Real.sqrt ((∫⁻ z in Ioc (-(1 / ((n : ℝ) + 1))) (0 : ℝ),
        ENNReal.ofReal (z ^ 2) ∂X.ν).toReal)) :
    ∀ t, CauchySeq (fun n => M n t) := by sorry
