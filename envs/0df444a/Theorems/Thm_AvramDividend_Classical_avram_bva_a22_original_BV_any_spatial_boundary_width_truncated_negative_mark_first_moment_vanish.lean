-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_BV_any_spatial_boundary_width_truncated_negative_mark_first_moment_vanish
-- name    : AvramDividend.Classical.avram_bva_a22_original_BV_any_spatial_boundary_width_truncated_negative_mark_first_moment_vanish
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T08:50:00.236494+00:00
-- url     : https://prove2.me/theorems/c91ee9c4-757b-4067-8168-944869125627
-- title:
--   Original BV truncated negative mark first moment near reserve zero vanishes for any shrinking spatial boundary sequence without a rate
-- statement:
--   For the genuine bounded-variation spectrally negative Levy source X, let ε(n) be any sequence of positive spatial boundary widths no larger than one and tending to zero, at any rate relative to physical clock refinements. The actual negative Levy first-moment boundary integral ∫_{z<0} min(ε(n),−z) ν(dz) tends to zero. This uses the Proved original BV source integrability of min(1,−z) and pinned dominated convergence, with pointwise limit zero on negative marks. It is a quantitative source ingredient for the BVA96 near-zero negative-jump spatial-tail control across arbitrary prescribed cofinal bands and requires neither finite negative activity nor global candidate generator L1. Additional stopped occupation-time source control is still necessary to complete BVA96.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_route_bv_drift9_original_spatial_truncated_first_moment_L1
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva_a22_original_BV_any_spatial_boundary_width_truncated_negative_mark_first_moment_vanish
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n ∧ ε n ≤ 1)
    (hεlim : Tendsto ε atTop (𝓝 (0 : ℝ))) :
    Tendsto
      (fun n => ∫ z in Iio (0 : ℝ), min (ε n) (-z) ∂X.ν)
      atTop (𝓝 (0 : ℝ)) := by sorry
