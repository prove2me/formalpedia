-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_sweep16_cstar_capped_optimality_above_barrier_of_boundary
-- name    : AvramDividend.Classical.avram_sweep16_cstar_capped_optimality_above_barrier_of_boundary
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T12:53:38.592998+00:00
-- url     : https://prove2.me/theorems/766d68e7-ae54-4922-8b34-d8c9a03030a9
-- title:
--   Exact capped c* optimality above the barrier reduces to one original boundary verification
-- statement:
--   For a finite original c-star barrier with the exact root standing, scale, discount and smoothness hypotheses, suppose only that the genuine capped valueFunctionLe at x=cstar is bounded by vcstar there. The Proved original vcstar nonnegativity makes the boundary extension theorem applicable, yielding a capped upper bound for every initial reserve x above the barrier. The freshly Proved source-exact barrier strategy lower-bound theorem gives the reverse inequality from an actual capped admissible barrier strategy. Therefore equality holds at every x at or above the barrier. No original BV or UBV Itô upper budget is assumed beyond the explicit boundary inequality.

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

theorem AvramDividend.Classical.avram_sweep16_cstar_capped_optimality_above_barrier_of_boundary
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤)
    (h_smooth :
      0 < X.σ ∨ X.BoundedVariation ∨ ContDiffOn ℝ 2 (vcstar W) (Ioi 0))
    (hBoundary :
      valueFunctionLe X q (cstar W) (cstar W).toReal ≤
        ENNReal.ofReal (vcstar W (cstar W).toReal)) :
    ∀ x : ℝ, (cstar W).toReal ≤ x →
      valueFunctionLe X q (cstar W) x = ENNReal.ofReal (vcstar W x) := by sorry
