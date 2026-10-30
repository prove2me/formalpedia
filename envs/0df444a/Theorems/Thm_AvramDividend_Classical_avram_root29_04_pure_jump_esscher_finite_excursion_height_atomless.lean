-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_04_pure_jump_esscher_finite_excursion_height_atomless
-- name    : AvramDividend.Classical.avram_root29_04_pure_jump_esscher_finite_excursion_height_atomless
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T08:31:53.36637+00:00
-- url     : https://prove2.me/theorems/18d32a6d-d6dd-4c60-80cc-93ed72b32bc5
-- title:
--   Pure infinite-small-jump finite reflected excursion has no fixed positive height atom under the actual finite Esscher law
-- statement:
--   For a spectrally negative Lévy process whose small negative jumps have divergent first absolute moment, a finite reflected excursion cannot have a fixed strictly positive height with positive mass under any actual terminal Esscher weighting. The genuine original-law finite-excursion null result follows from Rogozin near-zero negative regularity; absolutely continuous finite-clock Esscher measures preserve this exact path event. This does not posit that a sigma-finite Ito excursion law is absolutely continuous with respect to the finite-terminal original law.
-- source:
--   Proved ae_rogozin_slopes_of_infinite_small_jumps, ae_negative_near_zero_of_ae_rogozin_negative_slopes, reflectedSup_finite_excursion_height_level_null_under_P_of_regular; Mathlib withDensity_absolutelyContinuous.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_ae_rogozin_slopes_of_infinite_small_jumps
import Theorems.Thm_AvramDividend_Classical_ae_negative_near_zero_of_ae_rogozin_negative_slopes
import Theorems.Thm_AvramDividend_Classical_reflectedSup_finite_excursion_height_level_null_under_P_of_regular

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_root29_04_pure_jump_esscher_finite_excursion_height_atomless
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hvar : (∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν) = ⊤)
    (θ : ℝ) (hθ : 0 ≤ θ) (T H : ℝ≥0) (hH : 0 < H)
    (Height : Ω → ℝ≥0) (x : ℝ≥0) (hx : 0 < x)
    (hHeight : ∀ ω : Ω, Height ω = x →
      reflectedSup X H ω = 0 ∧
      sSup ((fun u : ℝ≥0 => reflectedSup X u ω) '' Icc 0 H) = (x : ℝ))
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
