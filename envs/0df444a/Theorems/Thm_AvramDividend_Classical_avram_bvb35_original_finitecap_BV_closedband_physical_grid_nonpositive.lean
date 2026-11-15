-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb35_original_finitecap_BV_closedband_physical_grid_nonpositive
-- name    : AvramDividend.Classical.avram_bvb35_original_finitecap_BV_closedband_physical_grid_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T17:15:17.022827+00:00
-- url     : https://prove2.me/theorems/2e6afac3-cf62-4fde-b7d4-2f9d3a1166b3
-- title:
--   Original BV finite-cap physical HJB generator signed mesh budget including zero and cap contact
-- statement:
--   On the ACTUAL original controlled prepayment left-limit spatial reserves at a finite nondecreasing deterministic physical mesh, suppose each reserve lies in [0,C]. The discounted time-increment weighted sum of the true physical BV drift×derivative (boundary coefficient 1) plus ORIGINAL compensated negative-mark generator integral minus q w is nonpositive, including exact reserve contacts at zero or finite cap. Use the unified closed-band compensated generator source bvb34 and positivity of physical mesh/time-discount weights. This is a full-mask pathwise original physical HJB nonpositivity certificate and preserves X,D,ν exactly.
-- source:
--   New bvb34 closed-band generator sign derived from Proved original boundary and interior HJB, for original source physical grid.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb35_original_finitecap_BV_closedband_physical_grid_nonpositive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hStanding : X.Standing)
    (hBV : X.BoundedVariation) (hActivity : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (hFinite : C ≠ ⊤)
    (hwCont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hwNeg : ∀ y : ℝ, y < 0 → w y = 0)
    (hwSmooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hwGen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hwGrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (u : ℕ → ℕ → ℝ≥0) (n : ℕ)
    (hGrid : ∀ i : ℕ, i ≤ n → u n i ≤ u n (i + 1))
    (hReserve : ∀ i : ℕ, i ≤ n →
      let z := Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
      0 ≤ z ∧ z ≤ C.toReal) :
    let Z : ℕ → ℝ := fun i => Function.leftLim
      (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
    (∑ i ∈ Finset.range (n + 1),
      Real.exp (-(q * (u n i : ℝ))) *
        (X.drift * (if Z i = 0 ∨ Z i = C.toReal then 1 else deriv w (Z i)) +
          (∫ z in Iio (0 : ℝ), w (Z i + z) - w (Z i) ∂X.ν) -
          q * w (Z i)) *
        ((u n (i + 1) : ℝ) - (u n i : ℝ))) ≤ 0 := by sorry
