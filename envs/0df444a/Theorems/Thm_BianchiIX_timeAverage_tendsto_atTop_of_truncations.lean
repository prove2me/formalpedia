-- Prove2me | Theorems.Thm_BianchiIX_timeAverage_tendsto_atTop_of_truncations
-- name    : BianchiIX.timeAverage_tendsto_atTop_of_truncations
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T18:30:40.698221+00:00
-- url     : https://prove2.me/theorems/a53f66ab-a625-41e5-8984-e3b215d95bbd
-- title:
--   Divergence of averages from convergent truncations
-- statement:
--   For a real sequence $u$, define
--   $$A_n(u)=\frac1n\sum_{j=0}^{n-1}u_j\quad(n\geq1),\qquad A_0(u)=0.$$
--
--   Suppose that, for each integer $R\geq0$, the averages of $\min(u_j,R)$
--   converge to $l_R$, and that $l_R\to+\infty$ as $R\to\infty$. Then
--   $$A_n(u)\longrightarrow+\infty.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/ObservableTransfer.lean#L22-L30

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

theorem BianchiIX.timeAverage_tendsto_atTop_of_truncations {u l : ℕ → ℝ}
    (htrunc : ∀ R : ℕ, Tendsto (timeAverage (fun j => min (u j) (R : ℝ))) atTop (𝓝 (l R)))
    (hl : Tendsto l atTop atTop) : Tendsto (timeAverage u) atTop atTop := by sorry
