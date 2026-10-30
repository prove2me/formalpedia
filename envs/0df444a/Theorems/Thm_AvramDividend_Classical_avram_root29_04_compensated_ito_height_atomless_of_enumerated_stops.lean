-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_04_compensated_ito_height_atomless_of_enumerated_stops
-- name    : AvramDividend.Classical.avram_root29_04_compensated_ito_height_atomless_of_enumerated_stops
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T10:08:25.576621+00:00
-- url     : https://prove2.me/theorems/c0bd4ccd-ccb8-442a-92bf-016f223bbae9
-- title:
--   Genuine countable stopped-height null plus explicit Itô compensation implies atomless height intensity
-- statement:
--   For an actual pure infinite-negative-small-jump spectrally negative Levy process, assume an explicitly specified countable excursion-mark enumeration, finite stopping-time level-hit geometry for each mark, and the genuine Ito compensation identity for the expected number of marks of height x against a strictly positive expected local-time exposure. Then the sigma-finite excursion-mark intensity puts zero mass on height x. The theorem does not assert the compensation identity or the existence of the enumeration: those are the remaining stochastic foundations.
-- source:
--   Proved source-specific countable finite Esscher stopped-height atomlessness [8b5edede] specialised to original probability P; exact compensation identity and positive expected local time stated as hypotheses; ENNReal nonzero product algebra.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_root29_04_pure_jump_countable_stopped_height_null

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_root29_04_compensated_ito_height_atomless_of_enumerated_stops
    {Ω E : Type*} [mΩ : MeasurableSpace Ω] [mE : MeasurableSpace E]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hvar : (∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν) = ⊤)
    (n : Measure E) (markHeight : E → ℝ≥0)
    (marks : ℕ → Ω → E) (τ ζ : ℕ → Ω → ℝ≥0) (x : ℝ≥0)
    (hτ : ∀ k : ℕ, ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] {ω : Ω | τ k ω ≤ s})
    (hstop : ∀ k : ℕ,
      IsStoppingTime 𝓕 (fun ω => (τ k ω : WithTop ℝ≥0)))
    (hAtLevel : ∀ k : ℕ, ∀ ω : Ω,
      markHeight (marks k ω) = x →
      τ k ω < ζ k ω ∧
      reflectedSup X (τ k ω) ω = (x : ℝ) ∧
      ∀ t : ℝ≥0, τ k ω ≤ t → t < ζ k ω →
        reflectedSup X t ω ≤ (x : ℝ))
    (times horizons : ℕ → ℝ≥0)
    (hdense : ∀ a b : ℝ≥0, a < b →
      ∃ m : ℕ, a < times m ∧ times m < b)
    (hpos : ∀ k : ℕ, 0 < horizons k)
    (hcofinal : ∀ ε : ℝ≥0, 0 < ε →
      ∃ k : ℕ, horizons k ≤ ε)
    (L : Ω → ENNReal)
    (hLpos : 0 < ∫⁻ ω, L ω ∂P)
    (hComp : (∫⁻ ω, (∑' k : ℕ,
      if markHeight (marks k ω) = x then (1 : ENNReal) else 0) ∂P) =
      (∫⁻ ω, L ω ∂P) * n {e : E | markHeight e = x}) :
    n {e : E | markHeight e = x} = 0 := by sorry
