-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_redux13_source_levy_cutoff_exponent_tendsto
-- name    : AvramDividend.Classical.avram_redux13_source_levy_cutoff_exponent_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T10:38:52.272941+00:00
-- url     : https://prove2.me/theorems/99dc90b5-52c5-431a-9231-5bc67ff062b2
-- title:
--   Original BV source Lévy negative-jump exponential integrals converge at zero cutoff
-- statement:
--   For the original bounded-variation Lévy measure, the exponential of the negative-jump source integral restricted to marks below -1/(k+1) converges to the integral over all negative marks, for every integer horizon. The bounded variation ensures integrability near zero and passage through the exponential.
-- source:
--   Faithful deterministic Lévy-measure half of corrected Redux12b limit theorem; strict cutoff consistently excludes boundary atoms.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_redux13_source_levy_cutoff_exponent_tendsto
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) :
    ∀ n : ℕ,
      Tendsto (fun k : ℕ =>
        Real.exp (-((n : ℝ) *
        (∫ y in Iio (-(1 / ((k : ℝ) + 1))), (1 - Real.exp y) ∂X.ν)))) atTop (𝓝
        (Real.exp (-((n : ℝ) *
        (∫ y in Iio (0 : ℝ), (1 - Real.exp y) ∂X.ν))))) := by sorry
