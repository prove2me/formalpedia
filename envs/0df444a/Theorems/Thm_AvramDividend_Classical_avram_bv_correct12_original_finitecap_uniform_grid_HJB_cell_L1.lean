-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_correct12_original_finitecap_uniform_grid_HJB_cell_L1
-- name    : AvramDividend.Classical.avram_bv_correct12_original_finitecap_uniform_grid_HJB_cell_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T08:23:10.490263+00:00
-- url     : https://prove2.me/theorems/16a169e6-880f-49bc-92ed-cf28f2555df9
-- title:
--   Original finite-activity BV HJB finite-cap grid cells are integrable without an additional B L1 premise
-- statement:
--   For the original Standing BV Levy process, finite activity and finite positive cap, every individual physical uniform-grid signed HJB generator cell from the original prepayment left-limit reserve is integrable. The value is masked to strict survival and positive subcap reserve. The proof combines the Proved exact original measurable-cell theorem c8437d69, finitecap residual lower 1ecef407 and uniform candidate bound 00de5b03; it requires no extra stochastic integrability premise on the generator or uncontrolled reserve. This is a directly importable original finite-horizon component of 8271cf4d and 3993433e.
-- source:
--   Nearest root-connected original finite-cap activity 8271cf4d needs automatic original uniform-grid HJB cell L1. This exact source family already has Proved measurability c8437d69 but lacks an automatic uniform integrable envelope; use newly Proved 1ecef407 and 00de5b03. Finite sum then integrable without extra hypothesis.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_candidate_one_sided_value_uniform_bound
import Theorems.Thm_AvramDividend_Classical_avram_bv_correct12_finitecap_generator_residual_floor
import Theorems.Thm_AvramDividend_Classical_avram_a19_generator_uniform_cell_aeStronglyMeasurable
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_correct12_original_finitecap_uniform_grid_HJB_cell_L1
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
    (n i : ℕ) (hi : i < n + 1) :
    Integrable (fun ω =>
      let Z : ℕ → ℝ := fun j => Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n j)
      if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
          0 < Z i ∧ ENNReal.ofReal (Z i) < C then
        Real.exp (-(q * (u n i : ℝ))) *
          (X.generator w (Z i) - q * w (Z i)) *
          ((u n (i + 1) : ℝ) - (u n i : ℝ))
      else 0) P := by sorry
