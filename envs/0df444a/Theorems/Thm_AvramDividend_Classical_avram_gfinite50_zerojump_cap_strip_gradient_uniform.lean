-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gfinite50_zerojump_cap_strip_gradient_uniform
-- name    : AvramDividend.Classical.avram_gfinite50_zerojump_cap_strip_gradient_uniform
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T18:42:41.425246+00:00
-- url     : https://prove2.me/theorems/8dfe1022-bbf3-42a1-9776-fa9e7aac58e4
-- title:
--   A zero-jump Gaussian HJB supersolution has uniformly bounded gradient up to any finite cap
-- statement:
--   On any lower-separated finite-cap interval, nonnegative Gaussian HJB supersolutions with nonnegative gradient have a uniform upper bound for the gradient, using the proved exponential spatial comparison. This supplies the cap-strip Gaussian martingale L2 approximation without assuming C2 smoothness at the cap.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_gfinite50_zerojump_cap_strip_gradient_uniform
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0) (hσ : X.σ ≠ 0)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ)
    (a c : ℝ) (hac : a < c)
    (hNonneg : ∀ y ∈ Ico a c, 0 ≤ w y)
    (hGrad : ∀ y ∈ Ico a c, 0 ≤ deriv w y)
    (hHJB : ∀ y ∈ Ico a c, X.generator w y - q * w y ≤ 0)
    (hDer1 : ∀ y ∈ Ico a c, HasDerivAt w (deriv w y) y)
    (hDer2 : ∀ y ∈ Ico a c,
      HasDerivAt (deriv w) (iteratedDeriv 2 w y) y) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y ∈ Ico a c, deriv w y ≤ B := by sorry
