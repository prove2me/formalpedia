-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_no_source_jumps_interval_probability
-- name    : AvramDividend.Classical.avram_wave4_04a_bv_actual_no_source_jumps_interval_probability
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T15:54:39.927523+00:00
-- url     : https://prove2.me/theorems/09830276-b998-4138-b22e-a01ad44981f6
-- title:
--   The actual original BV Lévy path has no genuine jumps on an interval with exact exponential probability
-- statement:
--   For the actual finite-activity bounded-variation spectrally negative Lévy source X, the probability that its literal original jump mark ΔX_u vanishes at every u∈(s,t] is exp(−(t−s)·X.ν((−∞,0))), for every s≤t. This is a first genuine source jump-count law, the zero-jump case, not merely the law of drift-deficient increments or a constructed Poisson process. It uses a P-a.s. exact equality between no genuine jumps and no drift-residual increment, plus the already Proved original-source residual zero atom. It remains short of the full count law, Borel mark bands, disjoint-band independence, predictable compensation and Lévy–Itô decomposition.
-- source:
--   Canonically Proved source residual zero-increment probability 5e61917b-ff60-41dd-8434-28d25b3707bc, monotone genuine residual f6cc1059-e8ca-403e-8d73-71a139d3dc4c, and strict residual jump iff actual X jump 7423dfee-c973-497f-a274-07e572cbd7a0. The source no-jump interval drift-only theorem 2a0cae7c-bb72-4e38-af57-cafabc83af01 is Open and must first become Proved. For fixed s≤t, choose positive T=t+1. On one full event, no X jumps⇒Y_t=Y_s. Conversely Y_t=Y_s and monotonicity exclude any strictly positive residual jump in (s,t], hence exclude any genuine X jump. Apply pinned MeasureTheory.measure_congr to a.e. equal subsets and then the Proved source residual zero atom.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_no_jump_interval_is_drift_only
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_residual_ae_monotone_all_times
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_source_nonzero_jump_iff_strict_drift_residual_jump
import Theorems.Thm_AvramDividend_Classical_bv_actual_residual_increment_zero_probability

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_04a_bv_actual_no_source_jumps_interval_probability
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (s t : ℝ≥0) (hst : s ≤ t) :
    P.real {ω : Ω |
      ∀ u : ℝ≥0, u ∈ Ioc s t →
        X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0} =
      Real.exp (-(((t - s : ℝ≥0) : ℝ) *
        (X.ν (Iio (0 : ℝ))).toReal)) := by sorry
