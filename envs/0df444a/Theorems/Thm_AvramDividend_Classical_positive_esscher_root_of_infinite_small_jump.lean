-- Prove2me | Theorems.Thm_AvramDividend_Classical_positive_esscher_root_of_infinite_small_jump
-- name    : AvramDividend.Classical.positive_esscher_root_of_infinite_small_jump
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T06:40:48.064606+00:00
-- url     : https://prove2.me/theorems/c5ec8641-473c-4cbe-960c-2929d46b99a7
-- title:
--   Infinite-small-jump Lévy processes have an unconditional positive Esscher root
-- statement:
--   Prove positive root ψ(φ)=q under zero Gaussian coefficient and divergent small-jump absolute first moment by combining proved conditional root crossing, proved canonical ψ continuity, and proved ψ(0)=0.
-- source:
--   Proved esscher_positive_root_of_gaussian / ..._of_infinite_small_jump; levy_laplace_exponent_continuousOn_nonnegative; levy_laplace_exponent_zero.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.positive_esscher_root_of_infinite_small_jump
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hσ : X.σ = 0)
    (hinf : (∫⁻ y in Ioo (-1 : ℝ) 0, ENNReal.ofReal |y| ∂X.ν) = ⊤)
    (q : ℝ) (hq : 0 < q) :
    ∃ φ : ℝ, 0 < φ ∧ X.ψ φ = q := by sorry
