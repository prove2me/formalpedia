-- Prove2me | Theorems.Thm_BianchiIX_timeAverage_mono
-- name    : BianchiIX.timeAverage_mono
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T18:23:27.32665+00:00
-- url     : https://prove2.me/theorems/009df483-a5d8-40e6-8bf5-a8ddf4184130
-- title:
--   Monotonicity of finite time averages
-- statement:
--   For a real sequence $u$, define
--   $$A_n(u)=\frac1n\sum_{j=0}^{n-1}u_j\quad(n\geq1),\qquad A_0(u)=0.$$
--
--   If $u_j\leq v_j$ for every $j$, then $A_n(u)\leq A_n(v)$ for every $n\geq0$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/ObservableTransfer.lean#L18-L20

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

theorem BianchiIX.timeAverage_mono {u v : ℕ → ℝ} (h : ∀ j, u j ≤ v j) (n : ℕ) :
    timeAverage u n ≤ timeAverage v n := by sorry
