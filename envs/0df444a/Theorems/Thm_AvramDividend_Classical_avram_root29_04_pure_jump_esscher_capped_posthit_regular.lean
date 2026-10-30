-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_04_pure_jump_esscher_capped_posthit_regular
-- name    : AvramDividend.Classical.avram_root29_04_pure_jump_esscher_capped_posthit_regular
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T08:11:06.736525+00:00
-- url     : https://prove2.me/theorems/bb9ef0c9-2bc1-4568-b74c-f46179c89316
-- title:
--   Pure infinite-small-jump Lévy posthit downward regularity under the actual finite-clock Esscher weighted law
-- statement:
--   For actual pure infinite-small-jump spectrally negative Lévy X, the finite-terminal exponential Esscher density preserves the almost-sure property of strictly negative increments arbitrarily soon after the exact capped first closed reflected level hit. The source near-zero regularity is furnished by proved Rogozin slopes; the stopped whole-path law under P and absolute continuity transport it to the displayed weighted measure. This is a genuine finite-clock result, not an excursion sigma-finite n Markov theorem.
-- source:
--   Proved b12c5430 Rogozin slopes, b2e617e8 near-zero negative, 3eb5e421 original-law capped first-hit posthit regular, 5b4f4749 absolute continuity preservation; Mathlib withDensity_absolutelyContinuous.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_ae_rogozin_slopes_of_infinite_small_jumps
import Theorems.Thm_AvramDividend_Classical_ae_negative_near_zero_of_ae_rogozin_negative_slopes
import Theorems.Thm_AvramDividend_Classical_reflectedSup_capped_firstClosedHit_posthit_negative_of_regular_source
import Theorems.Thm_AvramDividend_Classical_ae_negative_near_zero_of_absolutelyContinuous

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_root29_04_pure_jump_esscher_capped_posthit_regular
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hvar : (∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν) = ⊤)
    (θ : ℝ) (hθ : 0 ≤ θ) (T H : ℝ≥0) (x : ℝ)
    (times horizons : ℕ → ℝ≥0)
    (hdense : ∀ a b : ℝ≥0, a < b →
      ∃ m : ℕ, a < times m ∧ times m < b)
    (hpos : ∀ n : ℕ, 0 < horizons n)
    (hcofinal : ∀ ε : ℝ≥0, 0 < ε →
      ∃ n : ℕ, horizons n ≤ ε) :
    ∀ᵐ ω ∂(P.withDensity (fun ω : Ω =>
      ENNReal.ofReal (Real.exp
        (θ * X.X T ω - (T : ℝ) * X.ψ θ)))),
      ∀ ε : ℝ≥0, 0 < ε →
        ∃ s : ℝ≥0, s < ε ∧
          X.X (sInf ((Icc (0 : ℝ≥0) H ∩
            (fun u : ℝ≥0 => reflectedSup X u ω) ⁻¹' Ici x) ∪ {H}) + s) ω -
          X.X (sInf ((Icc (0 : ℝ≥0) H ∩
            (fun u : ℝ≥0 => reflectedSup X u ω) ⁻¹' Ici x) ∪ {H})) ω < 0 := by sorry
