-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_correct12_original_finitecap_HJB_grid_L1
-- name    : AvramDividend.Classical.avram_bv_correct12_original_finitecap_HJB_grid_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T08:44:45.968254+00:00
-- url     : https://prove2.me/theorems/05c43fa2-988e-4d77-9182-1c21dc132a33
-- title:
--   Original finite-cap BV full physical uniform generator grid sum is integrable
-- statement:
--   Under the exact original Standing BV finite-activity and finite-positive-cap assumptions, every finite sum of masked discounted HJB generator cells on the original prepayment left-limit physical uniform grid is integrable, without an additional uncontrolled generator or candidate value L1 hypothesis. Proved source-exact cell 16a169e6 applies termwise.
-- source:
--   Direct finite-sum aggregation of Proved original same-source individual HJB-cell integrability 16a169e6, as required by the finite-activity full-T source 8271cf4d.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_correct12_original_finitecap_uniform_grid_HJB_cell_L1

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_correct12_original_finitecap_HJB_grid_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFinite : C ≠ ⊤)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (hMass : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ) (hT : 0 < T)
    (u : ℕ → ℕ → ℝ≥0)
    (hgrid : ∀ n, u n 0 = 0 ∧
      ((u n (n + 1) : ℝ) = T - T / ((n : ℝ) + 2)))
    (hmono : ∀ n i, i < n + 1 → u n i ≤ u n (i + 1))
    (huniform : ∀ n i, (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2))
    (n : ℕ) :
    let cell : ℕ → Ω → ℝ := fun i ω =>
      let Z : ℕ → ℝ := fun j => Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n j)
      if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
          0 < Z i ∧ ENNReal.ofReal (Z i) < C then
        Real.exp (-(q * (u n i : ℝ))) *
          (X.generator w (Z i) - q * w (Z i)) *
          ((u n (i + 1) : ℝ) - (u n i : ℝ))
      else 0
    Integrable (fun ω => ∑ i ∈ Finset.range (n + 1), cell i ω) P := by sorry
