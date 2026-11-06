-- Prove2me | Theorems.Thm_BianchiIX_continuous_timeAverage_transfer
-- name    : BianchiIX.continuous_timeAverage_transfer
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T18:31:06.046472+00:00
-- url     : https://prove2.me/theorems/c50ffe3d-ddbb-4e4e-8ca6-3b903f0b52db
-- title:
--   Transfer of continuous averages between asymptotic sequences
-- statement:
--   For a real sequence $u$, define
--   $$A_n(u)=\frac1n\sum_{j=0}^{n-1}u_j\quad(n\geq1),\qquad A_0(u)=0.$$
--
--   Let $S\subset\mathbb R$ be compact and $f$ continuous on $S$. Suppose
--   $x_n,y_n\in S$, $x_n-y_n\to0$, and $A_n(f\circ y)\to l$. Then
--   $$A_n(f\circ x)\longrightarrow l.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/ObservableTransfer.lean#L50-L57

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

theorem BianchiIX.continuous_timeAverage_transfer {x y : ℕ → ℝ} {f : ℝ → ℝ} {l : ℝ}
    {S : Set ℝ} (hS : IsCompact S) (hf : ContinuousOn f S)
    (hx : ∀ n, x n ∈ S) (hy : ∀ n, y n ∈ S)
    (hxy : Tendsto (fun n => x n - y n) atTop (𝓝 0))
    (hl : Tendsto (timeAverage (fun n => f (y n))) atTop (𝓝 l)) :
    Tendsto (timeAverage (fun n => f (x n))) atTop (𝓝 l) := by sorry
