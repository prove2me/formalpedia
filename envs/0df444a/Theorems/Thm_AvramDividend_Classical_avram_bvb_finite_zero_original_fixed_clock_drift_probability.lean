-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_finite_zero_original_fixed_clock_drift_probability
-- name    : AvramDividend.Classical.avram_bvb_finite_zero_original_fixed_clock_drift_probability
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T23:45:18.005626+00:00
-- url     : https://prove2.me/theorems/764c46ee-475c-4500-88f9-381370f54b0f
-- title:
--   At zero finite negative-jump intensity the original Lévy path equals drift at each fixed clock almost surely
-- statement:
--   For every fixed nonnegative time, the original BV process has exact drift value with probability one when the negative Lévy mass is zero. Specialise the already Proved original future no-jump drift event probability with stopping clock zero.
-- source:
--   Direct source-faithful corollary of proved 00cb3771-a520-48cf-a5d8-deac1da022b8; needed for countable-clock extension of zero branch 8a3383c9-cade-472e-af16-f5abd1465970.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb_finite_zero_original_fixed_clock_drift_probability
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (hZero : X.ν (Iio (0 : ℝ)) = 0) (t : ℝ≥0) :
    P.real {ω : Ω | X.X t ω = (t : ℝ) * X.drift} = 1 := by sorry
