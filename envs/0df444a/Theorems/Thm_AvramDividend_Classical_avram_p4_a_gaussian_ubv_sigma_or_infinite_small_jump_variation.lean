-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_ubv_sigma_or_infinite_small_jump_variation
-- name    : AvramDividend.Classical.avram_p4_a_gaussian_ubv_sigma_or_infinite_small_jump_variation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T07:43:16.693019+00:00
-- url     : https://prove2.me/theorems/783949da-61e3-4575-9400-7179576dd861
-- title:
--   Original unbounded-variation Lévy source splits into positive Gaussian variance or infinite small-jump variation
-- statement:
--   For the actual original spectrally negative Lévy process, unbounded variation implies either a strictly positive same-source Gaussian coefficient σ or σ=0 together with infinite total variation of the original negative small-jump measure on (-1,0). This is the exhaustive branch condition needed before separate Gaussian and pure-jump UBV Itô-Meyer proofs; it constructs no Brownian process and requires no new semimartingale assumption.
-- source:
--   Authoritative AvramDividend_Classical_SpectrallyNegativeLevy.BoundedVariation and σ_nonneg fields; Avram–Palmowski–Pistorius, Section 3.1 and Proposition 4(i).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_a_gaussian_ubv_sigma_or_infinite_small_jump_variation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation) :
    (0 < X.σ) ∨
      (X.σ = 0 ∧
        (∫⁻ y in Ioo (-1 : ℝ) 0, ENNReal.ofReal |y| ∂X.ν) = ⊤) := by sorry
