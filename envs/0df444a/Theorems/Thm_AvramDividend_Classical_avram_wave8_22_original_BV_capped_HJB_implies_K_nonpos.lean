-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_capped_HJB_implies_K_nonpos
-- name    : AvramDividend.Classical.avram_wave8_22_original_BV_capped_HJB_implies_K_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:21:28.621944+00:00
-- url     : https://prove2.me/theorems/8cf2f343-d33e-4ad1-87ee-6a30dcd2bdfc
-- title:
--   Original capped BV physical HJB yields stopped generator nonpositivity below capital cap
-- statement:
--   The original Lévy generator sign follows directly on the capped positive predictable stopped region from the source HJB inequality restricted to 0<y and ENNReal.ofReal y<C. This matches the original dividend admissibility cap rather than assuming global HJB.
-- source:
--   Original Avram max-HJB restricted to positive capital below C, and original BV Lévy physical generator formula.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave8_22_original_BV_capped_HJB_implies_K_nonpos {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [SFinite P] {𝓕 : Filtration ℝ≥0 mΩ}
  (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
  (q : ℝ) (w : ℝ → ℝ) (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
  (A : Ω → Set ℝ≥0)
  (K : ℝ≥0 → Ω → ℝ)
  (hK : ∀ t ω, K t ω =
    Real.exp (-(q * (t : ℝ))) *
      (X.drift * deriv w (Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) +
      (∫ z in Iio (0 : ℝ),
        w (Function.leftLim (fun s : ℝ≥0 =>
            x + X.X s ω - rightLimit D s ω) t + z) -
        w (Function.leftLim (fun s : ℝ≥0 =>
            x + X.X s ω - rightLimit D s ω) t) ∂X.ν) -
      q * w (Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s ω - rightLimit D s ω) t)))
  (C : ℝ≥0∞)
  (hHJB : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
    X.drift * deriv w y +
      (∫ z in Iio (0 : ℝ), w (y + z) - w y ∂X.ν) -
      q * w y ≤ 0)
  (hRegion : ∀ᵐ ω ∂P, ∀ t, t ∈ A ω →
    0 < Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t ∧
    ENNReal.ofReal (Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) < C) :
  ∀ᵐ ω ∂P, ∀ t, t ∈ A ω → K t ω ≤ 0 := by sorry
