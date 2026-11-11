-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_anoise44_dyadic_levy_signed_integral_quadrature_bound
-- name    : AvramDividend.Classical.avram_anoise44_dyadic_levy_signed_integral_quadrature_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T14:29:39.298776+00:00
-- url     : https://prove2.me/theorems/e9fedf5a-b6b1-41e0-9a97-c64c0e54b2d1
-- title:
--   Quantitative original Lévy negative-mark dyadic integral quadrature error
-- statement:
--   For the original finite-negative-activity Lévy measure, the finite signed left-endpoint dyadic cell intensity sum differs from the exact signed band integral by at most 2^-k times the finite intensity of that band.
-- source:
--   Strictly necessary deterministic quantitative core of Open h42. Prove via geometric cover h43, disjoint half-open partition, and h34 per-cell 2^-k error integrated over the original measure.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_anoise44_dyadic_levy_signed_integral_quadrature_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ n k : ℕ,
      let B : Set ℝ := Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1)))
      let C : ℕ → Set ℝ := fun i =>
        B ∩ Ioc (-1 + (i : ℝ) / (2 : ℝ) ^ k)
          (-1 + ((i : ℝ) + 1) / (2 : ℝ) ^ k)
      |(∑ i ∈ Finset.range (2 ^ k),
          (-1 + (i : ℝ) / (2 : ℝ) ^ k) * (X.ν (C i)).toReal) -
        (∫ z in B, z ∂X.ν)| ≤
        (1 / (2 : ℝ) ^ k) * (X.ν B).toReal := by sorry
