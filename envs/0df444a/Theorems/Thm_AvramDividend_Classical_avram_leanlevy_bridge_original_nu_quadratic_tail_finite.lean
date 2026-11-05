-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_leanlevy_bridge_original_nu_quadratic_tail_finite
-- name    : AvramDividend.Classical.avram_leanlevy_bridge_original_nu_quadratic_tail_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T13:15:09.921221+00:00
-- url     : https://prove2.me/theorems/720bc49f-e337-417d-9696-2887ea5a1c75
-- title:
--   Original intrinsic Lévy ν small-band square energy is finite for every cutoff
-- statement:
--   For the actual Avram X.ν, every small-negative-jump annulus (-1/(n+1),0] has finite squared-mark Lévy energy. On this annulus z² ≤ min(1,z²), so the original spectral negative Lévy integrability hypothesis dominates the quadratic tail. This supplies the finite-tail premise needed to apply the public process-preserving ENNReal-to-real L2 Cauchy adapter.
-- source:
--   The finite dominating-integral comparison is extracted from the source-exact Proved e5cc5d15 vanishing quadratic tail proof, preserving original X.ν and the same interval convention.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_leanlevy_bridge_original_nu_quadratic_tail_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (n : ℕ) :
    (∫⁻ z in Ioc (-(1 / ((n : ℝ) + 1))) (0 : ℝ),
      ENNReal.ofReal (z ^ 2) ∂X.ν) ≠ ⊤ := by sorry
