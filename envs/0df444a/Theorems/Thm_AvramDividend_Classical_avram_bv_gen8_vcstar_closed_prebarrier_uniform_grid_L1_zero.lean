-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_gen8_vcstar_closed_prebarrier_uniform_grid_L1_zero
-- name    : AvramDividend.Classical.avram_bv_gen8_vcstar_closed_prebarrier_uniform_grid_L1_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T19:06:24.236359+00:00
-- url     : https://prove2.me/theorems/06f51fb8-3fc2-45b4-9bb2-fe27f236f8b2
-- title:
--   Uniform original BV grid generator L1 up to and including the optimal barrier
-- statement:
--   At each original BV physical grid the sum of all strictly positive stopped generator cells at or below the finite positive optimal barrier is identically zero and Integrable. The full cap-contact contribution is included under the explicit above-barrier generator condition from the source theorem; above-cap and zero-cap contributions remain distinct.
-- source:
--   Source-exact finite-grid consequence of 12d956d8, retaining the true original process, ruin clock and left-limit prestate.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_gen8_vcstar_closed_prebarrier_original_generator_cell_zero
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_gen8_vcstar_closed_prebarrier_uniform_grid_L1_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (hgen : ∀ y : ℝ, (cstar W).toReal < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        X.generator (vcstar W) y - q * vcstar W y ≤ 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (u : ℕ → ℕ → ℝ≥0) :
    let G : ℕ → ℕ → Ω → ℝ := fun n i ω =>
      let Z : ℝ := Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
      if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
          0 < Z ∧ Z ≤ (cstar W).toReal then
        Real.exp (-(q * (u n i : ℝ))) *
          (X.generator (vcstar W) Z - q * vcstar W Z) *
          ((u n (i + 1) : ℝ) - (u n i : ℝ))
      else 0
    ∀ n : ℕ,
      (∀ ω, (∑ i ∈ Finset.range (n + 1), G n i ω) = 0) ∧
      Integrable (fun ω => ∑ i ∈ Finset.range (n + 1), G n i ω) P := by sorry
