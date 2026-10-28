-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaled_piPathMeasure_eq_of_finite_pushforwards
-- name    : AvramDividend.Classical.scaled_piPathMeasure_eq_of_finite_pushforwards
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T15:32:56.699606+00:00
-- url     : https://prove2.me/theorems/a4f360a9-8051-434e-911a-4a2205fe532e
-- title:
--   Scaled equality of Pi-valued path laws from finite-dimensional marginals
-- statement:
--   If the finite-coordinate vector law of one measurable random path Y equals a fixed nonnegative scalar times that of another path Z for every finite coordinate set, then the complete path law of Y equals that same scalar multiple of the complete path law of Z, provided the first has finite mass.
-- source:
--   Applies the Proved unscaled finite-dimensional Pi-law uniqueness theorem ecb46b0d-f019-49bf-b243-60a156e4528f to the scalar-multiplied underlying measure using Mathlib Measure.map_smul. It is needed to promote the finite-dimensional stopped-history strong-Markov theorem 4a900fdc-a036-471d-bf4d-8e35ed1b2bfa to full shifted path law 61930a38-11f1-449e-bbb6-67d59c6d5ca8.

import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Constructions.Pi
import Theorems.Thm_AvramDividend_Classical_piPathMeasure_map_eq_of_finite_pushforwards

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.scaled_piPathMeasure_eq_of_finite_pushforwards
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω]
    {μ ν : Measure Ω}
    (Y Z : Ω → (ι → ℝ))
    (hY : Measurable Y) (hZ : Measurable Z)
    (c : ℝ≥0∞)
    (hMass : (Measure.map Y μ) Set.univ ≠ ⊤)
    (hFinite : ∀ J : Finset ι,
      Measure.map (fun ω : Ω => fun j : J => Y ω j) μ =
        c • Measure.map (fun ω : Ω => fun j : J => Z ω j) ν) :
    Measure.map Y μ = c • Measure.map Z ν := by
  sorry
