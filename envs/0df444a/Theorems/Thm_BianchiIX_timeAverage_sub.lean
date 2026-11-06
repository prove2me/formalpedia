-- Prove2me | Theorems.Thm_BianchiIX_timeAverage_sub
-- name    : BianchiIX.timeAverage_sub
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T18:22:58.651046+00:00
-- url     : https://prove2.me/theorems/160c75e9-7c7c-471b-b630-2782585d9f92
-- title:
--   Linearity of time averages under subtraction
-- statement:
--   For a real sequence $u$, define
--   $$A_n(u)=\frac1n\sum_{j=0}^{n-1}u_j\quad(n\geq1),\qquad A_0(u)=0.$$
--
--   For all real sequences $u,v$ and every $n\geq0$,
--   $$A_n(u-v)=A_n(u)-A_n(v).$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/ObservableTransfer.lean#L14-L16

import Definitions.Def_BianchiIX_Statistics_ObservableTransfer
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
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Topology.UniformSpace.HeineCantor

open Set Filter
open scoped Topology
open BianchiIX

theorem BianchiIX.timeAverage_sub (u v : ℕ → ℝ) (n : ℕ) :
    timeAverage (fun j => u j - v j) n = timeAverage u n - timeAverage v n := by sorry
