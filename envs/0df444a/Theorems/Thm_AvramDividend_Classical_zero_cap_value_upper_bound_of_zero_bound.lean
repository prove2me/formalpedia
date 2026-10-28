-- Prove2me | Theorems.Thm_AvramDividend_Classical_zero_cap_value_upper_bound_of_zero_bound
-- name    : AvramDividend.Classical.zero_cap_value_upper_bound_of_zero_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T21:54:44.068995+00:00
-- url     : https://prove2.me/theorems/a77b926c-06ed-4fc1-a8f4-945437968469
-- title:
--   Zero-cap verification at all nonnegative reserves reduces to reserve zero
-- statement:
--   The general zero-cap verification inequality for every nonnegative initial reserve is reduced to the cap-zero bound at reserve zero plus nonnegativity of the scale-function boundary candidate. For positive initial reserve, the canonically Proved valueFunctionLe_above_cap identity makes the optimal capped value the immediate surplus payment plus its value from zero. The canonically Proved barrierValue_zero_affine_nonnegative makes the scale candidate affine in exactly the same way. Addition monotonicity transfers the zero-reserve inequality. This directly supports the root-connected Open zero_cap_value_upper_bound (c019e4fa-dabb-4cb6-a906-33f150f0a179).
-- source:
--   Root-connected deterministic bridge from the zero-reserve optimal bound to all nonnegative reserves.

import Theorems.Thm_AvramDividend_Classical_valueFunctionLe_above_cap
import Theorems.Thm_AvramDividend_Classical_barrierValue_zero_affine_nonnegative
import Mathlib.Data.ENNReal.Basic

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.zero_cap_value_upper_bound_of_zero_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (W : ℝ → ℝ)
    (hzero : valueFunctionLe X q 0 0 ≤
      ENNReal.ofReal (barrierValue W 0 0))
    (hval : 0 ≤ barrierValue W 0 0)
    (x : ℝ) (hx : 0 ≤ x) :
    valueFunctionLe X q 0 x ≤ ENNReal.ofReal (barrierValue W 0 x) := by sorry
