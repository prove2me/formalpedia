-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_gen8_original_vcstar_full_grid_one_sided_majorant
-- name    : AvramDividend.Classical.avram_bv_gen8_original_vcstar_full_grid_one_sided_majorant
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T23:30:46.296071+00:00
-- url     : https://prove2.me/theorems/0f8c5b39-2dc4-46b9-8e00-e804c3daaf53
-- title:
--   Original full positive-reserve BV generator sum has an integrable clipped majorant of nonpositive mean
-- statement:
--   For the authentic stopped original Lévy BV physical grid, the candidate generator sum includes all positive pre-ruin cells, including above cstar. Under exact a.e. measurability, every bounded negative clipping is integrable, has nonpositive mean and dominates the untruncated signed source pointwise. No L1 claim is made for the untruncated source.
-- source:
--   Exact global source 1874dd49 and public clipped L1 c89d9a00, plus integral_nonpos_of_ae; retains precise measurability premise.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_gen8_original_vcstar_full_positive_cell_sign_and_cap_zero
import Theorems.Thm_AvramDividend_Classical_avram_bv_gen8_original_vcstar_clipped_finite_grid_integrable
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem AvramDividend.Classical.avram_bv_gen8_original_vcstar_full_grid_one_sided_majorant
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
    (hmono : ∀ n i, u n i ≤ u n (i + 1)) :
    let H : ℕ → ℕ → Ω → ℝ := fun n i ω =>
      let Z : ℝ := Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
      if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧ 0 < Z then
        Real.exp (-(q * (u n i : ℝ))) *
          (X.generator (vcstar W) Z - q * vcstar W Z) *
          ((u n (i + 1) : ℝ) - (u n i : ℝ))
      else 0
    (∀ n, AEStronglyMeasurable
      (fun ω => ∑ i ∈ Finset.range (n + 1), H n i ω) P) →
    ∀ (K : ℝ), 0 ≤ K →
      ∀ n, (Integrable (fun ω =>
        max (-K) (∑ i ∈ Finset.range (n + 1), H n i ω)) P ∧
      (∫ ω, max (-K) (∑ i ∈ Finset.range (n + 1), H n i ω) ∂P) ≤ 0) ∧
      ∀ ω, (∑ i ∈ Finset.range (n + 1), H n i ω) ≤
        max (-K) (∑ i ∈ Finset.range (n + 1), H n i ω) := by sorry
