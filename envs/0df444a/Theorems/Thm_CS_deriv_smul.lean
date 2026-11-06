-- Prove2me | Theorems.Thm_CS_deriv_smul
-- name    : CS.deriv_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:16:26.726203+00:00
-- url     : https://prove2.me/theorems/74a6709f-f7d6-4f30-84f6-5cfee1a3dd27
-- title:
--   CS: deriv smul
-- statement:
--   The CS construction uses the deriv smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/upstream-config/patches/PrimeNumberTheoremAnd-lean4341.patch#L91-L92
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/upstream-config/patches/PrimeNumberTheoremAnd-lean4341.patch#L91-L92

import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Definitions.Def_PrimeNumberTheoremAnd_Sobolev
set_option autoImplicit true
open Real Complex MeasureTheory Filter Topology BoundedContinuousFunction SchwartzMap  BigOperators
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
open CS
variable {f : CS n E} {R x v : ℝ}

theorem CS.deriv_smul {f : CS (n + 1) E} : (R • f).deriv = R • f.deriv := by sorry
