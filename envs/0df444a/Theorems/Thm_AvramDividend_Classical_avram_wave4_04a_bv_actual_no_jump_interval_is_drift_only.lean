-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_no_jump_interval_is_drift_only
-- name    : AvramDividend.Classical.avram_wave4_04a_bv_actual_no_jump_interval_is_drift_only
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T15:37:04.512488+00:00
-- url     : https://prove2.me/theorems/2a0cae7c-bb72-4e38-af57-cafabc83af01
-- title:
--   Every actual finite-activity BV Lévy interval without source jumps evolves by deterministic drift alone
-- statement:
--   On one original-source probability-one event for each finite horizon [0,T], if the actual spectrally negative Lévy X has no nonzero original-path jumps anywhere in a half-open interval (s,t], its drift residual d·t−X_t equals its initial value at s. Equivalently X_t−X_s=(t−s)·d exactly on the same sample path. This identifies a source drift-deficient grid interval with the presence of a genuine X jump, a key missing direction for grid-to-intrinsic count Poisson transfer. It does not claim that source jump counts are Poisson or compensated.
-- source:
--   Proved source finite residual range theorem 92aa24fb-9706-4627-ad59-287adbd329d0. Original fields X.leftLim, X.rightCont yield continuous sample paths at positive times where their left-limit jump mark vanishes. Thus X and the deterministic drift residual are continuous on an interval with no source jumps. Its image is contained in a finite set of residual values, discrete by pinned Set.Finite.isDiscrete, while Icc s t is preconnected by isPreconnected_Icc. Pinned IsPreconnected.constant_of_mapsTo implies residual equality. No unrelated Lévy construction is used.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_finite_residual_range_on_horizon

open MeasureTheory Filter Set Topology Finset AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_04a_bv_actual_no_jump_interval_is_drift_only
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, s ≤ t → t ≤ T →
      (∀ u : ℝ≥0, u ∈ Ioc s t →
        X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0) →
      (t : ℝ) * X.drift - X.X t ω =
        (s : ℝ) * X.drift - X.X s ω := by sorry
