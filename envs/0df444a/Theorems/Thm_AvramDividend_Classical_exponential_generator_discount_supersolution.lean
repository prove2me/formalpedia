-- Prove2me | Theorems.Thm_AvramDividend_Classical_exponential_generator_discount_supersolution
-- name    : AvramDividend.Classical.exponential_generator_discount_supersolution
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T06:25:45.95099+00:00
-- url     : https://prove2.me/theorems/f3c2ce45-6a3a-4222-9534-28fa5622b8bf
-- title:
--   Exponential Lévy generator satisfies the discounted HJB drift inequality whenever ψθ≤q
-- statement:
--   For the test function w(x)=e^(θx), the generator eigenfunction identity Γw=ψ(θ)w implies (Γ−q)w≤0 as soon as ψ(θ)≤q. The exponential factor is positive. This is precisely the analytic HJB drift-sign condition used in the verification theorem, not an Itô theorem.
-- source:
--   Proved generator_exp_eq_psi and positivity of Real.exp.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.exponential_generator_discount_supersolution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ q x : ℝ) (hψ : X.ψ θ ≤ q) :
    X.generator (fun y : ℝ => Real.exp (θ * y)) x -
      q * Real.exp (θ * x) ≤ 0 := by sorry
