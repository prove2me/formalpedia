-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb36_original_finitecap_BV_closedband_masked_physical_grid_nonpositive
-- name    : AvramDividend.Classical.avram_bvb36_original_finitecap_BV_closedband_masked_physical_grid_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T17:17:56.523855+00:00
-- url     : https://prove2.me/theorems/f75a469a-e73b-435e-b4d6-f1e8f88b7277
-- title:
--   Original BV finitecap inclusive zero/cap compensated HJB generator physical-grid cash source nonpositive under preruin mask
-- statement:
--   For an original Standing finiteactivity BV spectrally negative Lévy process and original admissible dividend D, at any monotone finite physical mesh, keep the ACTUAL original prepayment left-limit spatial reserve Z_i and original ruin time. Mask cells unless they are strictly pre-ruin and reserve Z_i lies in the entire CLOSED interval [0,C]. The original physical discounted drift×slope (using true boundary contact coefficient 1) plus the exact negative-mark compensated generator minus q w has nonpositive time-weighted sum for all paths. This is the inclusive boundary variant of the Proved original interior-only generator budget, needed for the full stopped original physical-grid BV source certificate.
-- source:
--   bvb34 original closed-band physical generator nonpositivity; original grid4 physical source.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb36_original_finitecap_BV_closedband_masked_physical_grid_nonpositive
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
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D) (ω : Ω)
    (u : ℕ → ℕ → ℝ≥0) (n : ℕ)
    (hGrid : ∀ i : ℕ, i ≤ n → u n i ≤ u n (i + 1)) :
    let Z : ℕ → ℝ := fun i => Function.leftLim
      (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
    (∑ i ∈ Finset.range (n + 1),
      if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
          0 ≤ Z i ∧ Z i ≤ C.toReal then
        Real.exp (-(q * (u n i : ℝ))) *
          (X.drift *
            (if Z i = 0 ∨ Z i = C.toReal then 1 else deriv w (Z i)) +
            (∫ z in Iio (0 : ℝ), w (Z i + z) - w (Z i) ∂X.ν) -
            q * w (Z i)) *
          ((u n (i + 1) : ℝ) - (u n i : ℝ))
      else 0) ≤ 0 := by sorry
