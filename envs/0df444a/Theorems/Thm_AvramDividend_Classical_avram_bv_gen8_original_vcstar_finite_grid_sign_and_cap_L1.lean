-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_gen8_original_vcstar_finite_grid_sign_and_cap_L1
-- name    : AvramDividend.Classical.avram_bv_gen8_original_vcstar_finite_grid_sign_and_cap_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T23:21:24.344765+00:00
-- url     : https://prove2.me/theorems/00cc6c2b-90ec-4a76-a713-0dff4a2013b1
-- title:
--   Original finite BV generator grid is nonpositive and its closed-cap part has zero L1
-- statement:
--   All original stopped physical BV generator HJB cells have a nonpositive finite-grid sum, while the exact suboptimal-cap-and-contact part has zero finite-grid sum and is integrable. Above-cap losses are allowed to be nonintegrable; this is a genuinely one-sided alternative to global L1.
-- source:
--   Folds source-exact full positive-cell sign with original cap-inclusive L1 zero certificate, explicitly separating the unbounded signed tail.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_gen8_original_vcstar_full_positive_cell_sign_and_cap_zero
import Theorems.Thm_AvramDividend_Classical_avram_bv_gen8_vcstar_closed_prebarrier_uniform_grid_L1_zero
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_gen8_original_vcstar_finite_grid_sign_and_cap_L1
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
    (∀ n ω, (∑ i ∈ Finset.range (n + 1), H n i ω) ≤ 0) ∧
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
