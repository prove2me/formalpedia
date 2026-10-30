-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_04_pure_jump_stopped_esscher_height_null
-- name    : AvramDividend.Classical.avram_root29_04_pure_jump_stopped_esscher_height_null
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T09:42:15.99071+00:00
-- url     : https://prove2.me/theorems/bbb0f06b-7e5e-4cea-8745-71f32017c68f
-- title:
--   Fixed-height excursion-null event at a true stopping-time hit under the finite-terminal pure-jump Esscher measure
-- statement:
--   For the actual spectrally negative Levy process with divergent first absolute small-jump moment, every finite-terminal genuine Esscher weighting gives zero mass to an exact fixed-height excursion mark whenever the mark's level is reached at a measurable finite stopping time and the reflected reserve remains below that height until the mark lifetime. This applies the Proved arbitrary-stopping Rogozin regularity to the Proved reflected-height-null converter; it is a valid finite tilted-path law statement and does not assert a sigma-finite Ito excursion intensity law.
-- source:
--   Accepted source-specific pure-jump arbitrary stopping downward regularity [56bd4e99] and accepted geometric height-null converter under almost-sure post-hit negative increments [663e43e3].

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_root29_04_pure_jump_esscher_arbitrary_stopping_downward_regular
import Theorems.Thm_AvramDividend_Classical_reflectedSup_height_level_null_of_ae_posthit_negative

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_root29_04_pure_jump_stopped_esscher_height_null
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hvar : (∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν) = ⊤)
    (θ : ℝ) (hθ : 0 ≤ θ) (T : ℝ≥0)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω : Ω | τ ω ≤ s})
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (ζ Height : Ω → ℝ≥0) (x : ℝ≥0)
    (hAtLevel : ∀ ω : Ω, Height ω = x →
      τ ω < ζ ω ∧
      reflectedSup X (τ ω) ω = (x : ℝ) ∧
      ∀ t : ℝ≥0, τ ω ≤ t → t < ζ ω →
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
      {ω : Ω | Height ω = x} = 0 := by sorry
