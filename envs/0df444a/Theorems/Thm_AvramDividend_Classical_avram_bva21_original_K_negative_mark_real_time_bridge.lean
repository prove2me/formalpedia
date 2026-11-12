-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva21_original_K_negative_mark_real_time_bridge
-- name    : AvramDividend.Classical.avram_bva21_original_K_negative_mark_real_time_bridge
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T21:57:18.147988+00:00
-- url     : https://prove2.me/theorems/9ace2e92-49d9-476b-aae1-3a28f1cd37f2
-- title:
--   Original K integral equals real-time integral of its exact capped discounted negative-mark kernel
-- statement:
--   The original stopped compensator K is the integral of the actual mark-restricted H over the time measure given by the pushforward of Lebesgue volume on [0,T]. Extract the negative-mark indicator, stopped cap mask and discount from the inner Lévy measure integral by the proved original mark factorisation lemma, then apply the proved real-time map-integral identity. The only additional hypothesis is a.e. strong measurability of the resulting original time integrand J, which must be established for the original bounded-variation path in the 7ccc2a1a parent.
-- source:
--   Source-exact K time-integral representation bridge required to apply paired dominated convergence to original compensator 7ccc2a1a.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bva21_negative_mark_restrict_indicator_extract
import Theorems.Thm_AvramDividend_Classical_avram_bvb_b21_original_time_map_integral
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva21_original_K_negative_mark_real_time_bridge
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (C τ : ℝ≥0∞) (U : ℝ≥0 → ℝ) (w : ℝ → ℝ)
    (q T : ℝ) (n : ℕ) :
    let B : ℝ≥0 → Prop := fun t =>
      0 < t ∧ (t : ℝ) < T - T / ((n : ℝ) + 2) ∧
      (t : ℝ≥0∞) ≤ τ ∧ 0 ≤ U t ∧ ENNReal.ofReal (U t) ≤ C
    let J : ℝ≥0 → ℝ := fun t =>
      if B t then Real.exp (-(q * (t : ℝ))) *
        (∫ z in Iio (0 : ℝ), w (U t + z) - w (U t) ∂X.ν) else 0
    let L : ℝ≥0 → ℝ := fun t =>
      ∫ z : ℝ, (if B t ∧ z < 0 then
        Real.exp (-(q * (t : ℝ))) * (w (U t + z) - w (U t)) else 0)
        ∂(X.ν.restrict (Iio (0 : ℝ)))
    AEStronglyMeasurable J
      (((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal) →
    (∫ t : ℝ≥0, L t
      ∂(((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal)) =
    ∫ r in Icc (0 : ℝ) T, J (Real.toNNReal r) := by sorry
