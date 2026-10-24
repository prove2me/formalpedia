-- Prove2me | Theorems.Thm_AvramDividend_Classical_excursion_capped_laplace_bounded_nnreal_test
-- name    : AvramDividend.Classical.excursion_capped_laplace_bounded_nnreal_test
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T23:09:07.760885+00:00
-- url     : https://prove2.me/theorems/1ad23c92-379f-4307-9f61-7985ce726291
-- title:
--   Capped Laplace exponential is an NNReal bounded continuous weak-convergence test
-- statement:
--   This helper constructs a bounded continuous NNReal-valued version of the Laplace test x ↦ exp(-s max(x,0)), for s ≥ 0. It uses the already Proved real-valued continuity and range estimates, and the diameter bound of the NNReal codomain to supply the exact test type expected by the probability weak-convergence criterion.
-- source:
--   Capped Laplace integrands and bounded-continuous tests, Prove2Me Avram dividend Chat01.

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Tactic.Linarith

open Topology

theorem AvramDividend.Classical.excursion_capped_laplace_bounded_nnreal_test
    (s : ℝ) (hs : 0 ≤ s) :
    ∃ f : BoundedContinuousFunction ℝ NNReal,
      ∀ x : ℝ, (f x : ℝ) = Real.exp (-(s * max x 0)) := by sorry
