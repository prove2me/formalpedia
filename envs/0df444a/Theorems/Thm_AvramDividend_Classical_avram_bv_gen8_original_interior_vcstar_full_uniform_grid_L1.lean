-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_gen8_original_interior_vcstar_full_uniform_grid_L1
-- name    : AvramDividend.Classical.avram_bv_gen8_original_interior_vcstar_full_uniform_grid_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T09:43:40.110676+00:00
-- url     : https://prove2.me/theorems/11474761-35d7-41c8-983c-424a81a98e88
-- title:
--   Original full strict-interior cstar BV generator grid is identically zero and L1, any dividend strategy
-- statement:
--   For arbitrary original dividend control and stopped physical-grid times, the exact strict interior cstar generator-residual cells add to zero, giving L1 integrability uniformly across every finite grid. The proof is a genuine finite-sum reduction to the source-exact individual cell certificate avram_bv_gen8_original_vcstar_generator_interior_cell_L1_any_grid.
-- source:
--   Genuine source-exact finite-sum assembly reduction into the original-process cellwise L1 theorem. The child is the only nontrivial dependency; finite sums of pointwise zero functions vanish and are integrable.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_gen8_original_interior_vcstar_full_uniform_grid_L1
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
    ∀ n, (∀ ω, (∑ i ∈ Finset.range (n + 1), H n i ω) = 0) ∧
      Integrable (fun ω => ∑ i ∈ Finset.range (n + 1), H n i ω) P := by sorry
