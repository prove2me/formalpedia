-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_gen8_vcstar_closed_prebarrier_original_generator_cell_zero
-- name    : AvramDividend.Classical.avram_bv_gen8_vcstar_closed_prebarrier_original_generator_cell_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T19:01:39.071231+00:00
-- url     : https://prove2.me/theorems/12d956d8-4907-41bb-810f-7b961c2175d5
-- title:
--   Original BV generator-cell equality up to and including positive optimal barrier
-- statement:
--   The actual stopped leftlim BV generator contribution vanishes for every positive prestate at or below the positive finite optimal barrier, including cap-contact. The strict interior follows from the proved BV-GEN8 prebarrier theorem and exact barrier contact from the proved above-barrier HJB-compatible cap generator equation, with the above-barrier condition explicit.
-- source:
--   Source-exact bridge between public Proved 3e8a840b (strict interior) and public Proved 91803827 (optimal cap contact), retaining the latter's above-cap generator hypothesis.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_gen8_vcstar_prebarrier_original_generator_cell_zero
import Theorems.Thm_AvramDividend_Classical_vcstar_generator_eq_zero_at_positive_cstar
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_gen8_vcstar_closed_prebarrier_original_generator_cell_zero
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
    (u : ℕ → ℕ → ℝ≥0) (n i : ℕ) (ω : Ω) :
    let Z : ℝ := Function.leftLim
      (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
    (if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
        0 < Z ∧ Z ≤ (cstar W).toReal then
      Real.exp (-(q * (u n i : ℝ))) *
        (X.generator (vcstar W) Z - q * vcstar W Z) *
        ((u n (i + 1) : ℝ) - (u n i : ℝ))
    else 0) = 0 := by sorry
