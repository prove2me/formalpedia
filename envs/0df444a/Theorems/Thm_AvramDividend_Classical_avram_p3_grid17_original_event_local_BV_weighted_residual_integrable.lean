-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid17_original_event_local_BV_weighted_residual_integrable
-- name    : AvramDividend.Classical.avram_p3_grid17_original_event_local_BV_weighted_residual_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T21:41:17.842211+00:00
-- url     : https://prove2.me/theorems/b02d05bb-4e36-4570-905f-e5abe142f768
-- title:
--   Authentic BV Lévy drift residual is integrable on any measurable coefficient-bounded physical grid event
-- statement:
--   For the exact bounded-variation spectrally negative Lévy residual R(t) formed from drift, original process and true downward jump sum, any finite physical grid weighted by measurable coefficients is integrable after restriction to a measurable event where those coefficients are bounded by a fixed deterministic K. The proof reuses the already Proved clipped original residual theorem and agrees pointwise with the unclipped source on the event. This bridge enables joint adaptive P3-GRID16 masks to isolate the integrable derivative-weighted R part of canonical B without imposing a global coefficient bound.
-- source:
--   Original-process direct extension of public Proved 6b976cb7-43e7-46d4-9c1d-1f7771ba42bd; motivated by canonical 0b2da5b3 and joint events fa593bb7.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_clipped_weighted_R_mesh_L1

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid17_original_event_local_BV_weighted_residual_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (T : ℝ≥0) (u : ℕ → ℕ → ℝ≥0) (n : ℕ)
    (hu : ∀ i, i < n + 1 → u n i ≤ u n (i + 1))
    (hu0 : u n 0 = 0) (huT : u n (n + 1) ≤ T)
    (a : Ω → ℕ → ℝ)
    (hMeasA : ∀ i, Measurable (fun ω => a ω i))
    (s : Set Ω) (hs : MeasurableSet s)
    (K : ℝ) (hK : 0 ≤ K)
    (hBound : ∀ ω ∈ s, ∀ i ∈ Finset.range (n + 1), |a ω i| ≤ K) :
    Integrable (fun ω => if ω ∈ s then
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) -
          (∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
          else 0)
      ∑ i ∈ Finset.range (n + 1),
        a ω i * (R (u n i) - R (u n (i + 1)))
    else 0) P := by sorry
