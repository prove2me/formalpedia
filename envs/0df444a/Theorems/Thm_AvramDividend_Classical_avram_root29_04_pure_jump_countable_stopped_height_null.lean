-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_04_pure_jump_countable_stopped_height_null
-- name    : AvramDividend.Classical.avram_root29_04_pure_jump_countable_stopped_height_null
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T09:58:23.818652+00:00
-- url     : https://prove2.me/theorems/8b5edede-0c9c-46e3-8d81-e113fe02aaeb
-- title:
--   Countable family of exact stopped-excursion heights is null under genuine finite Esscher laws
-- statement:
--   For the actual spectrally negative Levy process in the infinite-small-jump branch, and any countable sequence of finite measurable stopping times with excursion heights whose level-event implies genuine posthit maximum geometry, the genuine finite-terminal Esscher law assigns zero mass to the union of exact-height marks. This is a probability path-law statement; an Ito excursion enumeration and sigma-finite intensity law are distinct unproved interfaces.
-- source:
--   Canonically Proved pure-jump finite Esscher stopped-height atomlessness [bbb0f06b] and pinned Mathlib measure_iUnion_null for countable index.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_root29_04_pure_jump_stopped_esscher_height_null

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_root29_04_pure_jump_countable_stopped_height_null
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hvar : (∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν) = ⊤)
    (θ : ℝ) (hθ : 0 ≤ θ) (T : ℝ≥0)
    (τ ζ Height : ℕ → Ω → ℝ≥0) (x : ℝ≥0)
    (hτ : ∀ k : ℕ, ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] {ω : Ω | τ k ω ≤ s})
    (hstop : ∀ k : ℕ,
      IsStoppingTime 𝓕 (fun ω => (τ k ω : WithTop ℝ≥0)))
    (hAtLevel : ∀ k : ℕ, ∀ ω : Ω, Height k ω = x →
      τ k ω < ζ k ω ∧
      reflectedSup X (τ k ω) ω = (x : ℝ) ∧
      ∀ t : ℝ≥0, τ k ω ≤ t → t < ζ k ω →
        reflectedSup X t ω ≤ (x : ℝ))
    (times horizons : ℕ → ℝ≥0)
    (hdense : ∀ a b : ℝ≥0, a < b →
      ∃ m : ℕ, a < times m ∧ times m < b)
    (hpos : ∀ n : ℕ, 0 < horizons n)
    (hcofinal : ∀ ε : ℝ≥0, 0 < ε →
      ∃ n : ℕ, horizons n ≤ ε) :
    (P.withDensity (fun ω : Ω =>
      ENNReal.ofReal (Real.exp
        (θ * X.X T ω - (T : ℝ) * X.ψ θ))))
      (⋃ k : ℕ, {ω : Ω | Height k ω = x}) = 0 := by sorry
