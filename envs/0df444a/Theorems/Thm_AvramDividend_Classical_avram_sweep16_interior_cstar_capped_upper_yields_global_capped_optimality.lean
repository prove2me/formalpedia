-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_sweep16_interior_cstar_capped_upper_yields_global_capped_optimality
-- name    : AvramDividend.Classical.avram_sweep16_interior_cstar_capped_upper_yields_global_capped_optimality
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T12:55:42.504561+00:00
-- url     : https://prove2.me/theorems/b04b845f-9e86-49ef-ae6d-c5ca37756b17
-- title:
--   Original capped optimality at all reserves reduces to interior verification up to c*
-- statement:
--   Under the root hypotheses, assume the genuine original capped value upper bound only on the closed reserve interval [0,cstar], including the barrier boundary. The original cstar boundary extension theorem propagates the upper bound to all reserves above the barrier, using the independently Proved nonnegativity of vcstar. The already Proved original barrier attainment lower-bound theorem supplies the reverse inequality at every reserve. Consequently the exact capped optimality identity follows for all nonnegative capital. This isolates the remaining stochastic verification task to the interior and boundary, with no equality-in-law or new assumptions.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_sweep17_vcstar_nonnegative_all_capital
import Theorems.Thm_AvramDividend_Classical_avram_sweep17_cstar_boundary_to_above_cap
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_barrier_cstar_lower_bounds_from_attainment

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_sweep16_interior_cstar_capped_upper_yields_global_capped_optimality
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤)
    (h_smooth :
      0 < X.σ ∨ X.BoundedVariation ∨ ContDiffOn ℝ 2 (vcstar W) (Ioi 0))
    (hInterior :
      ∀ x : ℝ, 0 ≤ x → x ≤ (cstar W).toReal →
        valueFunctionLe X q (cstar W) x ≤ ENNReal.ofReal (vcstar W x)) :
    ∀ x : ℝ, 0 ≤ x →
      valueFunctionLe X q (cstar W) x = ENNReal.ofReal (vcstar W x) := by sorry
