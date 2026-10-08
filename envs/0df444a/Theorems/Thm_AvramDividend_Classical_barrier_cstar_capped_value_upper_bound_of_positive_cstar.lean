-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrier_cstar_capped_value_upper_bound_of_positive_cstar
-- name    : AvramDividend.Classical.barrier_cstar_capped_value_upper_bound_of_positive_cstar
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T17:50:43.556977+00:00
-- url     : https://prove2.me/theorems/8ce07d6a-4364-4218-81d5-d4f1f0e8a23f
-- title:
--   Capped verification upper bound when c-star is positive
-- statement:
--   For a positive finite c*, Proposition 4(i) applied to v_{c*} gives the capped value upper bound for initial reserves at or below c*. For x>c*, the established above-cap decomposition splits off the compulsory initial dividend x-c* and reduces the comparison to the boundary value at c*. This isolates the positive-barrier branch of Theorem 2(i).
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 4(i) and proof of Theorem 2(i), pp. 17-20, together with the compulsory initial-excess identity for the formal cap convention.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

namespace AvramDividend.Classical

theorem barrier_cstar_capped_value_upper_bound_of_positive_cstar
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨ ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) :
    ∀ x : ℝ, 0 ≤ x →
      valueFunctionLe X q (cstar W) x ≤ ENNReal.ofReal (vcstar W x) := by
  sorry

end AvramDividend.Classical
