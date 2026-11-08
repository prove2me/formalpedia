-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_gen8_full_vcstar_grid_zero_of_leftLim_cap
-- name    : AvramDividend.Classical.avram_bv_gen8_full_vcstar_grid_zero_of_leftLim_cap
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T08:43:27.345681+00:00
-- url     : https://prove2.me/theorems/adf5d6d0-8f4c-4c6c-8c05-68d149e071e8
-- title:
--   Original capped left-limit paths have identically zero and integrable full BV generator grids
-- statement:
--   For the actual spectrally negative Lévy process, if every active original physical stopped left-limit reserve is at most cstar, the entire full discounted generator grid vanishes pathwise, giving L1 without a compensated jump estimate. Its cap assumption will be discharged by the separate original reserve certificate a009975c.
-- source:
--   Exact Proved original above-cstar generator support c907dc0e. This source-specific cap implication is independent of the still Open post-payment left-limit cap a009975c and is the second child of the candidate-specific integrability route.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_gen8_original_vcstar_cell_supported_strict_above_cap

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_gen8_full_vcstar_grid_zero_of_leftLim_cap
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
    (u : ℕ → ℕ → ℝ≥0)
    (hZcap : ∀ n i ω, (u n i : ℝ≥0∞) < ruinTime X x D ω →
      Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i) ≤
        (cstar W).toReal) :
    let H : ℕ → ℕ → Ω → ℝ := fun n i ω =>
      let Z : ℝ := Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
      if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧ 0 < Z then
        Real.exp (-(q * (u n i : ℝ))) *
          (X.generator (vcstar W) Z - q * vcstar W Z) *
          ((u n (i + 1) : ℝ) - (u n i : ℝ))
      else 0
    ∀ n, (∀ ω, (∑ i ∈ Finset.range (n + 1), H n i ω) = 0) ∧
      Integrable (fun ω => ∑ i ∈ Finset.range (n + 1), H n i ω) P := by sorry
