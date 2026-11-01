-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_source_jump_times_have_uniform_positive_separation_ae
-- name    : AvramDividend.Classical.avram_wave4_04a_bv_actual_source_jump_times_have_uniform_positive_separation_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T19:20:59.991881+00:00
-- url     : https://prove2.me/theorems/1edc0870-08fc-4455-91c9-6edc0702656e
-- title:
--   Actual original finite-activity BV Lévy jump times have strictly positive pairwise mesh separation on each finite horizon almost surely
-- statement:
--   For the actual BV source SpectrallyNegativeLevy X with finite total negative jump intensity, at every positive finite horizon T on a P-full event there is a strictly positive real δ(ω,T) such that any two distinct actual nonzero jump times in (0,T] differ in metric distance by at least δ. This establishes the source-specific mesh-separation prerequisite needed to prove that sufficiently fine original-X grids contain at most one genuine source jump per cell. The result uses the original Ω, P and same X, not a constructed Poisson process, and does not yet prove eventual grid count equality or a compensator.
-- source:
--   Canonical Proved original-X jump-time finiteness 6a65718c-c002-4f92-98e7-85d17ced83e5. For each finite set of true jump times, form the finite set of metric distances over ordered unequal pairs. If there are pairs, its finite minimum is positive because each distinct pair has positive distance; otherwise any positive δ works. This is a constructive finite-set argument in the original path, using pinned Mathlib Finset.min'_mem, Finset.min'_le and dist_pos. No Lévy-law replacement or filtration transport.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_04a_bv_actual_source_jump_times_have_uniform_positive_separation_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ ω ∂P, ∃ δ : ℝ, 0 < δ ∧
      ∀ u v : ℝ≥0,
        (u ≤ T ∧ 0 < u ∧ X.X u ω -
          Function.leftLim (fun w : ℝ≥0 => X.X w ω) u ≠ 0) →
        (v ≤ T ∧ 0 < v ∧ X.X v ω -
          Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0) →
        u ≠ v → δ ≤ dist u v := by sorry
