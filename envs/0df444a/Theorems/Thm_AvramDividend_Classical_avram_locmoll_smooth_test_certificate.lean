-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_locmoll_smooth_test_certificate
-- name    : AvramDividend.Classical.avram_locmoll_smooth_test_certificate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T19:06:31.916129+00:00
-- url     : https://prove2.me/theorems/2e269e44-0ec4-4d09-bac9-26533bf1d8ab
-- title:
--   Smooth one-sided test functions preserving the Lévy generator inequality
-- statement:
--   Use a globally monotone unit-slope extension of the original candidate and smooth with positive shifts supported inside the lower strip. Prove actual generator interchange for the Lévy triplet (including small and large marks), global smoothness, positivity and the gradient constraint. The restricted convolution secant is supplied by a separate proved lemma.
-- source:
--   Avram–Palmowski–Pistorius (2007), Proposition 4(i), exact parent d6c4b57e-8c2e-4e7b-85e3-9f961dd52d12

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_locmoll_smooth_test_certificate
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (δ : ℝ) (hδ : 0 < δ) (hδx : δ < x) :
    ∃ (V ρ g : ℝ → ℝ),
      Integrable ρ ∧ (∫ r, ρ r) = 1 ∧
      (0 ≤ᵐ[volume] ρ) ∧
      (∀ᵐ r ∂volume, ρ r ≠ 0 →
        r ∈ Icc (δ / 3) (2 * (δ / 3))) ∧
      (∀ u v : ℝ, 0 ≤ u → u ≤ v → v - u ≤ V v - V u) ∧
      (∀ y : ℝ, Integrable (fun r => ρ r * V (y - r))) ∧
      (∀ y : ℝ, g y = ∫ r, ρ r * V (y - r)) ∧
      ContDiff ℝ 2 g ∧ MonotoneOn g (Ici 0) ∧
      (∀ y : ℝ, 0 ≤ g y) ∧
      (∀ y : ℝ, y ≤ 0 → g y = 0) ∧
      (∀ y : ℝ, δ ≤ y → 1 ≤ deriv g y) ∧
      (∀ y : ℝ, δ ≤ y → ENNReal.ofReal y ≤ C →
        X.GeneratorIntegrable g y ∧ X.generator g y - q * g y ≤ 0) ∧
      g x ≤ w x := by sorry
