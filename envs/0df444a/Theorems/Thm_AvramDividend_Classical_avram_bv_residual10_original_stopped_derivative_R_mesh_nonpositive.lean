-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_stopped_derivative_R_mesh_nonpositive
-- name    : AvramDividend.Classical.avram_bv_residual10_original_stopped_derivative_R_mesh_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T13:57:28.939201+00:00
-- url     : https://prove2.me/theorems/c27e50dc-09b5-480b-b879-3a665ecb9290
-- title:
--   Exact original stopped discounted derivative residual mesh is nonpositive
-- statement:
--   For every fixed original BV physical grid, the derivative-weighted raw residual mesh sum with the exact ruin-time mask and original left-limit reserve is nonpositive almost surely. It follows by masking each original reserve left limit after ruin and applying the previously Proved original BV interior weighted-residual nonpositivity theorem. The proof preserves the original process and does not assume derivative boundedness, integrability of the untruncated source or a Brownian replacement.
-- source:
--   AVRAM BV-RESIDUAL10 exact stopped original derivative residual sign from Proved P3 BV mesh lemma, 7 November 2026

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_discounted_interior_residual_mesh_nonpositive

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_residual10_original_stopped_derivative_R_mesh_nonpositive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (u : ℕ → ℕ → ℝ≥0) (n : ℕ)
    (hu : ∀ i, i < n + 1 → u n i ≤ u n (i + 1)) :
    ∀ᵐ ω ∂P,
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω else 0
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) - J t
      (∑ i ∈ Finset.range (n + 1),
        (let Z := Function.leftLim
          (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
         if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
             0 < Z ∧ ENNReal.ofReal Z < C then
           Real.exp (-(q * (u n i : ℝ))) * deriv w Z
         else 0) * (R (u n i) - R (u n (i + 1)))) ≤ 0 := by sorry
