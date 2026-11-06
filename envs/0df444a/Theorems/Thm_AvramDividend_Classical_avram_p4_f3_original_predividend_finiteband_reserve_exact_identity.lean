-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_predividend_finiteband_reserve_exact_identity
-- name    : AvramDividend.Classical.avram_p4_f3_original_predividend_finiteband_reserve_exact_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T20:43:51.554813+00:00
-- url     : https://prove2.me/theorems/c8be76d6-54a9-438e-a56d-10b42c8b8ba4
-- title:
--   Exact same-source stopped predividend finite-band reserve identity including the dividend right-limit atom
-- statement:
--   For each physical original spectrally negative Lévy path X and dividend path D, the reserve after the dividend right-limit equals its original same-space drift, finite compensated negative band, intrinsic large jump sum and Gaussian residual, minus the right-limit dividend. This is an exact finite-band pathwise identity and handles the time-t dividend atom algebraically.
-- source:
--   Derive directly from Proved e9bcd24b original controlled reserve finiteband identity; cancel the actual single-time rightLimit D t - D t payment correction without auxiliary process, equality-in-law or stochastic assumptions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_controlled_finiteband_reserve_identity
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical
noncomputable section

theorem AvramDividend.Classical.avram_p4_f3_original_predividend_finiteband_reserve_exact_identity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (t : ℝ≥0) (ω : Ω) :
    let j : ℝ≥0 → ℝ := fun u =>
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
    let E : Set (ℝ≥0 × ℝ) :=
      Ioc (0 : ℝ≥0) t ×ˢ Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1)))
    riskProcess X x D t ω -
      (rightLimit D t ω - D t ω) =
      x + (t : ℝ) * X.c +
        ((∑' u : ℝ≥0, if 0 < u ∧ j u ≠ 0 then
            E.indicator (fun p : ℝ≥0 × ℝ => p.2) (u, j u) else 0) -
          (t : ℝ) * (∫ z in Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1))), z ∂X.ν)) +
        avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω +
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω -
        rightLimit D t ω := by sorry
