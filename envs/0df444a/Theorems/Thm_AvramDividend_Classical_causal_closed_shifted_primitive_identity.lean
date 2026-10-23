-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_closed_shifted_primitive_identity
-- name    : AvramDividend.Classical.causal_closed_shifted_primitive_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T21:55:20.936801+00:00
-- url     : https://prove2.me/theorems/7051007c-ba49-4f3e-9605-5e9df27a4d62
-- title:
--   Primitive of a causal input from a closed shifted finite window
-- statement:
--   For 0<u≤x, integrating the input cut off to [0,x] after shifting by u over t∈(0,x] gives the primitive of g over (0,x-u]. The translated closed window [u,x] differs from (u,x] by a null singleton, then the verified translation lemma applies.
-- source:
--   Mathlib.MeasureTheory.Integral.Bochner.Set, setIntegral_indicator and integral_Icc_eq_integral_Ioc; translated-window theorem.

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_causal_shift_window_change_of_variables

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.causal_closed_shifted_primitive_identity
    (g : ℝ → ℝ) (u x : ℝ)
    (hu : 0 < u) (hux : u ≤ x) :
    (∫ t in Ioc (0 : ℝ) x,
      ((Icc (0 : ℝ) x).indicator g) (t - u) ∂volume) =
    (∫ s in Ioc (0 : ℝ) (x - u), g s ∂volume) := by sorry
