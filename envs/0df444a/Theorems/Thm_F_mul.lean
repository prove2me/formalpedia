-- Prove2me | Theorems.Thm_F_mul
-- name    : F_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:34:10.380515+00:00
-- url     : https://prove2.me/theorems/f93e7af3-1d2c-4ad8-8494-7ba4858cd5b8
-- title:
--   F mul: F mul
-- statement:
--   The F mul construction uses the F mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/upstream-config/patches/PrimeNumberTheoremAnd-lean4341.patch#L26-L28
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/upstream-config/patches/PrimeNumberTheoremAnd-lean4341.patch#L26-L28

import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Definitions.Def_PrimeNumberTheoremAnd_Sobolev
import Definitions.Def_PrimeNumberTheoremAnd_Fourier
set_option autoImplicit true
open FourierTransform Real Complex MeasureTheory Filter Topology BoundedContinuousFunction
  SchwartzMap VectorFourier BigOperators

theorem F_mul {f : ℝ → ℂ} {c : ℂ} {u : ℝ} :
    𝓕 (fun x => c * f x) u = c * 𝓕 f u := by sorry
