-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_gen8_original_interior_vcstar_grid_expected_zero
-- name    : AvramDividend.Classical.avram_bv_gen8_original_interior_vcstar_grid_expected_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T09:50:36.269812+00:00
-- url     : https://prove2.me/theorems/ade9156c-41e6-4526-afe6-40b6c89d6089
-- title:
--   Original BV strict-interior capped value generator grid has zero expectation
-- statement:
--   The original stopped physical grid generator-minus-discount contribution of the cstar candidate has zero expectation at every finite grid, for arbitrary original dividend processes and grids, provided only that cells are sampled at positive strict interior surplus. This is the expectation bridge downstream from the source-exact full-grid L1 reduction.
-- source:
--   Uses the Proved or accepted-sketch original strict-interior vcstar full uniform-grid pointwise identity 11474761; a pointwise zero integrand has zero Lebesgue integral.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_gen8_original_interior_vcstar_grid_expected_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (u : ℕ → ℕ → ℝ≥0) :
    let H : ℕ → ℕ → Ω → ℝ := fun n i ω =>
      let Z : ℝ := Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
      if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
          0 < Z ∧ ENNReal.ofReal Z < cstar W then
        Real.exp (-(q * (u n i : ℝ))) *
          (X.generator (vcstar W) Z - q * vcstar W Z) *
          ((u n (i + 1) : ℝ) - (u n i : ℝ))
      else 0
    ∀ n, (∫ ω, ∑ i ∈ Finset.range (n + 1), H n i ω ∂P) = 0 := by sorry
