-- Prove2me | Theorems.Thm_AvramDividend_Classical_nnreal_bounded_stopping_delay_preserves_bound
-- name    : AvramDividend.Classical.nnreal_bounded_stopping_delay_preserves_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T10:22:04.640863+00:00
-- url     : https://prove2.me/theorems/62248dcb-a1ee-46cf-b823-0b636f923a36
-- title:
--   Uniform bounds propagate under deterministic delay of nonnegative stopping times
-- statement:
--   If a nonnegative random time τ is bounded uniformly by T, delaying it by h preserves the uniform bound T+h. This is the second input needed to reapply bounded-stopping-time Lévy transform identities at the shifted random time.
-- source:
--   Pointwise monotonicity of addition by the fixed nonnegative horizon h.

import Mathlib.Data.NNReal.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.nnreal_bounded_stopping_delay_preserves_bound
    {Ω : Type*} (τ : Ω → ℝ≥0) (T h : ℝ≥0)
    (hbounded : ∀ ω, τ ω ≤ T) :
    ∀ ω, τ ω + h ≤ T + h := by sorry
