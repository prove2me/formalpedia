-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a22_original_BV_finite_negative_activity_physical_levy_ito_exact
-- name    : AvramDividend.Classical.avram_a22_original_BV_finite_negative_activity_physical_levy_ito_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T13:29:10.3692+00:00
-- url     : https://prove2.me/theorems/1617c0ff-c258-4829-968e-e454b65956fc
-- title:
--   Exact physical original BV Lévy-Ito source from original drift, large jumps and compensated small-negative jump limit
-- statement:
--   For the actual original spectrally negative bounded-variation Lévy process with finite negative-jump activity and Standing, prove its sample path equals t*c plus the original uncompensated large negative-mark integral plus the original full small-negative-band compensated limit Jsmall, on one full-measure event for all horizons. This is physical source Lévy–Itô identification, no new Gaussian process or artificial stochastic diagonal. Use original exact BV physical drift/jump path dcda0213 and actual source compensator identity.
-- source:
--   Avram Palmowski Pistorius (2007), Proposition 4(i), original source finite-activity BV construction; Kyprianou Chapter 2 Levy-Ito; original Proved dcda0213 physical drift and jump path, and compensated negative-mark source definitions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_a22_original_BV_finite_negative_activity_physical_levy_ito_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (Jsmall : ℝ≥0 → Ω → ℝ)
    (hJ : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
        atTop (𝓝 (Jsmall t ω))) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      X.X t ω = (t : ℝ) * X.c +
        avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω +
        Jsmall t ω := by sorry
