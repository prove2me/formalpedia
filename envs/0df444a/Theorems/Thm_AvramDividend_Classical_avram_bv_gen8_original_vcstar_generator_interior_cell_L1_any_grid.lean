-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_gen8_original_vcstar_generator_interior_cell_L1_any_grid
-- name    : AvramDividend.Classical.avram_bv_gen8_original_vcstar_generator_interior_cell_L1_any_grid
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T09:41:09.869178+00:00
-- url     : https://prove2.me/theorems/6a4124b4-90f9-436e-9d14-3f9198e2ea3b
-- title:
--   Every original stopped interior-cstar BV generator cell vanishes and is L1 on any physical grid
-- statement:
--   For the original stopped BV Levy process, every discounted generator cell sampled only at strictly interior positive reserve Z below cstar is identically zero and integrable for arbitrary dividend process and time-grid values. Reuses source-exact interior cstar q-harmonicity and does not require admissibility, cap or an above-barrier generator bound.
-- source:
--   Original exact grid generator cell of canonical d2ca06c0 specialised at w=vcstar and C=cstar. Proved by b196c9ff plus 0458283a and ENNReal conversion; requires no Stieltjes or jump martingale assumptions.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_gen8_original_vcstar_generator_interior_cell_L1_any_grid
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (u : ℕ → ℕ → ℝ≥0) :
    ∀ n i,
      let H : Ω → ℝ := fun ω =>
        let Z : ℝ := Function.leftLim
          (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
        if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
            0 < Z ∧ ENNReal.ofReal Z < cstar W then
          Real.exp (-(q * (u n i : ℝ))) *
            (X.generator (vcstar W) Z - q * vcstar W Z) *
            ((u n (i + 1) : ℝ) - (u n i : ℝ))
        else 0
      (∀ ω, H ω = 0) ∧ Integrable H P := by sorry
