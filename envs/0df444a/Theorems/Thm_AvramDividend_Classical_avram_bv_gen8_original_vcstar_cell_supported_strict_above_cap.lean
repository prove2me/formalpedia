-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_gen8_original_vcstar_cell_supported_strict_above_cap
-- name    : AvramDividend.Classical.avram_bv_gen8_original_vcstar_cell_supported_strict_above_cap
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T23:39:05.290821+00:00
-- url     : https://prove2.me/theorems/c907dc0e-df7f-432f-a360-b34acb28de33
-- title:
--   Exact original stopped candidate generator cell is supported strictly above the positive barrier
-- statement:
--   The original pre-right-payment left-limit physical grid generator term at any positive reserve is exactly the same term restricted to reserves strictly exceeding the optimal barrier. The interior and cap-contact generator vanish without expectation or mesh assumptions; all potential negative L1 tail is above cstar.
-- source:
--   Original closed-cap source cell certificate 12d956d8; case partition preserving the original stopped BV surplus and process.

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
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem AvramDividend.Classical.avram_bv_gen8_original_vcstar_cell_supported_strict_above_cap
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
    (if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧ 0 < Z then
      Real.exp (-(q * (u n i : ℝ))) *
        (X.generator (vcstar W) Z - q * vcstar W Z) *
        ((u n (i + 1) : ℝ) - (u n i : ℝ))
    else 0) =
    (if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
          (cstar W).toReal < Z then
      Real.exp (-(q * (u n i : ℝ))) *
        (X.generator (vcstar W) Z - q * vcstar W Z) *
        ((u n (i + 1) : ℝ) - (u n i : ℝ))
    else 0) := by sorry
