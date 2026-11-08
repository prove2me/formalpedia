-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_stopped_clipped_derivative_mesh_L1
-- name    : AvramDividend.Classical.avram_bv_residual10_original_stopped_clipped_derivative_mesh_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T12:43:56.41659+00:00
-- url     : https://prove2.me/theorems/223c3c1b-38c0-4789-b763-3bc19f1152ab
-- title:
--   Original stopped discounted derivative mesh becomes L1 under finite coefficient clipping
-- statement:
--   The exact original spectrally negative Levy prepayment reserve left limit, strict ruin-time indicator, derivative of the admissible test function, discounted grid coefficient and literal raw BV remainder are retained. For any finite uniform physical row n and any finite coefficient clipping level K >= 0, the clipped stochastic weighted raw-R mesh is integrable. Measurability of the authentic masked derivative coefficient comes from the already Proved original-process cell theorem, the uniform grid is bounded before T, and integrability follows from the genuine original raw remainder clipped-grid bridge. This does not assert integrability of the untruncated coefficient or remove the separate small-jump/tail obligation.
-- source:
--   AVRAM BV-RESIDUAL10 exact stopped derivative clipped original uniform-grid L1, 7 November 2026

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_a19_nonint_original_masked_derivative_grid_cell_measurable
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_clipped_weighted_R_mesh_L1

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_residual10_original_stopped_clipped_derivative_mesh_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
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
    (T : ℝ) (hT : 0 < T)
    (u : ℕ → ℕ → ℝ≥0)
    (hgrid : ∀ n, u n 0 = 0 ∧
      ((u n (n + 1) : ℝ) = T - T / ((n : ℝ) + 2)))
    (hmono : ∀ n i, i < n + 1 → u n i ≤ u n (i + 1))
    (huniform : ∀ n i, (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2))
    (n : ℕ) (K : ℝ) (hK : 0 ≤ K) :
    Integrable (fun ω =>
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω else 0
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) - J t
      let Z : ℕ → ℝ := fun i => Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
      ∑ i ∈ Finset.range (n + 1),
        (let a : ℝ :=
          if i < n + 1 then
            if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
                0 < Z i ∧ ENNReal.ofReal (Z i) < C then
              Real.exp (-(q * (u n i : ℝ))) * deriv w (Z i)
            else 0
          else 0
         if |a| ≤ K then a else 0) *
          (R (u n i) - R (u n (i + 1)))) P := by sorry
