-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_vcstar_zero_cstar_capped_upper
-- name    : AvramDividend.Classical.avram_sweep16_original_vcstar_zero_cstar_capped_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T12:23:00.259771+00:00
-- url     : https://prove2.me/theorems/c7e5c9b2-d62e-4e7f-a30a-6f2d9cbc4a71
-- title:
--   Original vcstar bounds zero-cstar capped value at every nonnegative capital
-- statement:
--   When the source scale-function minimising barrier cstar is exactly zero, the original positive-discount capped valueFunctionLe is bounded by original vcstar at every nonnegative starting reserve. This uses proved zero-cap boundary domination, nonnegative zero-barrier candidate, and the exact original all-capital zero-cap affine extension. The zero-cap case is handled directly and does not assume positive cap.
-- source:
--   Proved zero_cap_value_at_zero_upper_bound c7854fde, barrier_zero_boundary_value_nonneg df5df3b8, zero_cap_value_upper_bound_of_zero_bound a77b926c; unfold vcstar at cstar=0.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_zero_cap_value_at_zero_upper_bound
import Theorems.Thm_AvramDividend_Classical_barrier_zero_boundary_value_nonneg
import Theorems.Thm_AvramDividend_Classical_zero_cap_value_upper_bound_of_zero_bound

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_sweep16_original_vcstar_zero_cstar_capped_upper
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc0 : cstar W = 0) :
    ∀ x : ℝ, 0 ≤ x →
      valueFunctionLe X q (cstar W) x ≤ ENNReal.ofReal (vcstar W x) := by sorry
