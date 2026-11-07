-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_gen8_vcstar_prebarrier_uniform_grid_L1_zero
-- name    : AvramDividend.Classical.avram_bv_gen8_vcstar_prebarrier_uniform_grid_L1_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T18:54:17.552198+00:00
-- url     : https://prove2.me/theorems/3301f5b1-fb2a-4176-84ca-9f3671dec01a
-- title:
--   Uniform original stopped BV grid prebarrier generator sum has zero L1 mass
-- statement:
--   At every finite physical mesh, the exact original stopped generator loss restricted to strictly positive states below the optimal positive barrier sums identically to zero, hence its total grid mass is integrable for every mesh and stopping clock. It isolates the prebarrier BV generator regime; cap-contact and above-barrier regimes still require separate treatment.
-- source:
--   Source-exact finite-grid consequence of public Proved 3e8a840b; no assumption of arbitrary w generator L1.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_gen8_vcstar_prebarrier_original_generator_cell_zero
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_gen8_vcstar_prebarrier_uniform_grid_L1_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : 0 < cstar W)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (u : ℕ → ℕ → ℝ≥0) :
    let G : ℕ → ℕ → Ω → ℝ := fun n i ω =>
      let Z : ℝ := Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
      if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
          0 < Z ∧ Z < (cstar W).toReal then
        Real.exp (-(q * (u n i : ℝ))) *
          (X.generator (vcstar W) Z - q * vcstar W Z) *
          ((u n (i + 1) : ℝ) - (u n i : ℝ))
      else 0
    ∀ n : ℕ,
      (∀ ω, (∑ i ∈ Finset.range (n + 1), G n i ω) = 0) ∧
      Integrable (fun ω => ∑ i ∈ Finset.range (n + 1), G n i ω) P := by sorry
