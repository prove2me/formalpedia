-- Prove2me | Theorems.Thm_F_neg
-- name    : F_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:34:12.121191+00:00
-- url     : https://prove2.me/theorems/9ce4e7ef-e13f-4aca-8d4d-14c404526f75
-- title:
--   F neg: F neg
-- statement:
--   The F neg construction uses the F neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/upstream-config/patches/PrimeNumberTheoremAnd-lean4341.patch#L15-L16
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/upstream-config/patches/PrimeNumberTheoremAnd-lean4341.patch#L15-L16

import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Definitions.Def_PrimeNumberTheoremAnd_Sobolev
import Definitions.Def_PrimeNumberTheoremAnd_Fourier
set_option autoImplicit true
open FourierTransform Real Complex MeasureTheory Filter Topology BoundedContinuousFunction
  SchwartzMap VectorFourier BigOperators

theorem F_neg {f : ℝ → ℂ} {u : ℝ} : 𝓕 (fun x => -f x) u = - 𝓕 f u := by sorry
