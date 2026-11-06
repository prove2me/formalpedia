-- Prove2me | Theorems.Thm_BianchiIX_timeAverage_finsetSum
-- name    : BianchiIX.timeAverage_finsetSum
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T19:36:09.977251+00:00
-- url     : https://prove2.me/theorems/3cfce08f-5571-4856-9c66-dfd60862cb55
-- title:
--   Finite sums commute with finite time averages
-- statement:
--   For a real sequence $u$, define
--   $$A_n(u)=\frac1n\sum_{j=0}^{n-1}u_j\quad(n\geq1),\qquad A_0(u)=0.$$
--   For a finite set $s\subset I$, real sequences
--   $u_i$, and every $N\in\mathbb N$,
--   $$A_N\left(j\mapsto\sum_{i\in s}u_i(j)\right)
--   =\sum_{i\in s}A_N(u_i).$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/GaussDigitStatistics.lean#L13-L16

import Definitions.Def_BianchiIX_Statistics_ObservableTransfer
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.Dynamics.BirkhoffSum.Average
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.List.Induction
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.PNat.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Data.Rat.Floor
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.OrderIsoNat
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Dynamics.BirkhoffSum.NormedSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set

open Set Filter MeasureTheory
open scoped Topology
open BianchiIX
noncomputable section
open InverseBranchTree.BranchEstimates

theorem BianchiIX.timeAverage_finsetSum {ι : Type*} (s : Finset ι) (u : ι → ℕ → ℝ) (N : ℕ) :
    timeAverage (fun j => ∑ i ∈ s, u i j) N = ∑ i ∈ s, timeAverage (u i) N := by sorry
