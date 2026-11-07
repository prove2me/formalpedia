-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_gen8_original_vcstar_grid_supported_strict_above_cap
-- name    : AvramDividend.Classical.avram_bv_gen8_original_vcstar_grid_supported_strict_above_cap
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T23:45:52.567718+00:00
-- url     : https://prove2.me/theorems/ce7194ee-43fd-49d4-9ff4-19b0bea03f22
-- title:
--   Full original stopped BV generator grid equals exactly its strictly-above-barrier contribution
-- statement:
--   The full physical BV generator finite sum, using the original pre-right-payment reserve and ruin clock, is exactly the sum of contributions from reserves strictly above cstar. The source identity is pathwise for all physical grids, without requiring measurability or L1. This identifies the only possible negative generator tail for the barrier candidate.
-- source:
--   Derived by finite-sum congruence from the exact original above-cstar support theorem.

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
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem AvramDividend.Classical.avram_bv_gen8_original_vcstar_grid_supported_strict_above_cap
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
    let H : ℕ → ℕ → Ω → ℝ := fun n i ω =>
      let Z : ℝ := Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
      if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧ 0 < Z then
        Real.exp (-(q * (u n i : ℝ))) *
          (X.generator (vcstar W) Z - q * vcstar W Z) *
          ((u n (i + 1) : ℝ) - (u n i : ℝ))
      else 0
    let J : ℕ → ℕ → Ω → ℝ := fun n i ω =>
      let Z : ℝ := Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
      if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
          (cstar W).toReal < Z then
        Real.exp (-(q * (u n i : ℝ))) *
          (X.generator (vcstar W) Z - q * vcstar W Z) *
          ((u n (i + 1) : ℝ) - (u n i : ℝ))
      else 0
    ∀ n ω, (∑ i ∈ Finset.range (n + 1), H n i ω) =
      ∑ i ∈ Finset.range (n + 1), J n i ω := by sorry
