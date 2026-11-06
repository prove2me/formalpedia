-- Prove2me | Theorems.Thm_BianchiIX_continuous_observable_difference
-- name    : BianchiIX.continuous_observable_difference
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T18:23:52.583827+00:00
-- url     : https://prove2.me/theorems/c3005596-28c3-4d86-a42c-59c04c3c47bd
-- title:
--   Continuous observables preserve asymptotic agreement on compact sets
-- statement:
--   Let $S\subset\mathbb R$ be compact, let $f$ be continuous on $S$,
--   and let $x_n,y_n\in S$. If $x_n-y_n\to0$, then $f(x_n)-f(y_n)\to0$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/ObservableTransfer.lean#L32-L43

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

theorem BianchiIX.continuous_observable_difference {x y : ℕ → ℝ} {f : ℝ → ℝ}
    {S : Set ℝ} (hS : IsCompact S) (hf : ContinuousOn f S)
    (hx : ∀ n, x n ∈ S) (hy : ∀ n, y n ∈ S)
    (hxy : Tendsto (fun n => x n - y n) atTop (𝓝 0)) :
    Tendsto (fun n => f (x n) - f (y n)) atTop (𝓝 0) := by sorry
