-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_dense_simple_centering_extension
-- name    : AvramDividend.Classical.avram_wave4_p1_dense_simple_centering_extension
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T19:16:05.96658+00:00
-- url     : https://prove2.me/theorems/8ea36a3f-d8b0-41a2-b87d-49179cf54138
-- title:
--   Centering of elementary predictable integrals extends to all L² kernels by density
-- statement:
--   Given a genuinely dense real submodule S of predictable elementary L² integrands and a continuous linear integral I from the full L² domain V to the L² random-variable space W, prove that every continuous linear mean or bounded-past-test L:W→ℝ vanishes on all I(V) if it vanishes on I(S). In genuine stochastic applications, the elementary zero-mean/conditional-mean property is derived from Poisson past/future law, not assumed globally. Prove by density and closedness of the zero-level set of L∘I. Does not assume the sought martingale property for the full integral.
-- source:
--   Pinned Mathlib DenseRange.induction, isClosed_eq, ContinuousLinearMap.continuous. Independent of source-X actual compensator; complements the separately pending P1 L² completion interface.

import Mathlib

open MeasureTheory

theorem AvramDividend.Classical.avram_wave4_p1_dense_simple_centering_extension
    {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (S : Submodule ℝ V)
    (hDense : DenseRange S.subtype)
    (I : V →L[ℝ] W)
    (L : W →L[ℝ] ℝ)
    (hElementary : ∀ x : S, L (I (x : V)) = 0) :
    ∀ v : V, L (I v) = 0 := by sorry
