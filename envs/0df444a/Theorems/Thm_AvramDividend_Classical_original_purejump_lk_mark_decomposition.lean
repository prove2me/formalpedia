-- Prove2me | Theorems.Thm_AvramDividend_Classical_original_purejump_lk_mark_decomposition
-- name    : AvramDividend.Classical.original_purejump_lk_mark_decomposition
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:54:20.344393+00:00
-- url     : https://prove2.me/theorems/7a6e6fc3-ceff-4a31-b81a-d1e2b60ae6aa
-- title:
--   Original compensated Lévy–Khintchine mark algebra at the truncation cutoff
-- statement:
--   Given original standing pure-jump spectrally negative process and integrability of the compensated exponential primitive, split the exact original Lévy–Khintchine real integral at y=-1 and show ψ(θ)/θ equals original drift plus original signed large-mark first moment plus the integral of the common compensated primitive. The source uses exact exponential FTC primitive, including the atom at -1 on the large-mark side.
-- source:
--   Original laplaceExponent and new compensated_jump_exponential_primitive (89643c46); signed large-mark Proved 0e758fb9; source target 0fded7ba.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.original_purejump_lk_mark_decomposition
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hσ : X.σ = 0) (θ : ℝ) (hθ : 0 < θ)
    (hFn : Integrable
      (fun y : ℝ => ∫ t in (0 : ℝ)..(-y), 1 - Real.exp (-θ * t)) X.ν) :
    X.ψ θ / θ =
      X.c + (∫ y in Iic (-1 : ℝ), y ∂X.ν) +
      (∫ y : ℝ, ∫ t in (0 : ℝ)..(-y),
        1 - Real.exp (-θ * t) ∂X.ν) := by sorry
