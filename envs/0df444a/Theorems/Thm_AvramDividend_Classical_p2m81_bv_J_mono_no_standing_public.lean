-- Prove2me | Theorems.Thm_AvramDividend_Classical_p2m81_bv_J_mono_no_standing_public
-- name    : AvramDividend.Classical.p2m81_bv_J_mono_no_standing_public
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T05:44:54.667952+00:00
-- url     : https://prove2.me/theorems/c58c0c04-fe43-4bc5-8fce-3a21f3f9f0ee
-- title:
--   Compensated small-jump integrals are monotone in Laplace parameter
-- statement:
--   For a spectrally negative Levy process, the normalised compensated small-jump integrals J(θ) are monotone nondecreasing in θ>0, with no Standing or BV assumption. Helper D2 isolating the J-mono step of the drift-positive eventual-growth argument.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.p2m81_bv_J_mono_no_standing_public
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    ∀ θ₁ θ₂ : ℝ, 0 < θ₁ → θ₁ ≤ θ₂ →
      (∫ y : ℝ, (Real.exp (θ₁ * y) - 1 - θ₁ * y) / θ₁ ∂(X.ν.restrict (Ioo (-1 : ℝ) 0))) ≤ (∫ y : ℝ, (Real.exp (θ₂ * y) - 1 - θ₂ * y) / θ₂ ∂(X.ν.restrict (Ioo (-1 : ℝ) 0))) := by sorry
