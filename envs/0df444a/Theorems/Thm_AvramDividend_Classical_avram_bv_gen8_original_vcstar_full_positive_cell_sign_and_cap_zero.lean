-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_gen8_original_vcstar_full_positive_cell_sign_and_cap_zero
-- name    : AvramDividend.Classical.avram_bv_gen8_original_vcstar_full_positive_cell_sign_and_cap_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T23:11:05.980486+00:00
-- url     : https://prove2.me/theorems/1874dd49-141b-432b-af43-b070872d7926
-- title:
--   Original stopped BV physical generator cells are nonpositive globally and zero through positive optimal cap
-- statement:
--   For the actual stopped BV surplus on every nondecreasing physical mesh and positive optimal finite barrier, all positive-reserve discounted generator cells are nonpositive, and every cell inside or exactly at the optimal barrier vanishes. The above-cap HJB bound is an explicit hypothesis; no global generator L1 is asserted.
-- source:
--   Source-exact bridge from Proved global HJB edf09308 to accepted/public BV-GEN8 cap-inclusive zero 12d956d8, with true leftLim and ruinTime.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_vcstar_hjb_all_positive_of_generator
import Theorems.Thm_AvramDividend_Classical_avram_bv_gen8_vcstar_closed_prebarrier_original_generator_cell_zero
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_gen8_original_vcstar_full_positive_cell_sign_and_cap_zero
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
    (∀ n i ω, H n i ω ≤ 0) ∧
      ∀ n i ω,
        let Z : ℝ := Function.leftLim
          (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
        (if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
            0 < Z ∧ Z ≤ (cstar W).toReal then
          Real.exp (-(q * (u n i : ℝ))) *
            (X.generator (vcstar W) Z - q * vcstar W Z) *
            ((u n (i + 1) : ℝ) - (u n i : ℝ))
        else 0) = 0 := by sorry
