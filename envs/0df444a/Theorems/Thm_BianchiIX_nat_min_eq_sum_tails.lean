-- Prove2me | Theorems.Thm_BianchiIX_nat_min_eq_sum_tails
-- name    : BianchiIX.nat_min_eq_sum_tails
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T19:36:15.25071+00:00
-- url     : https://prove2.me/theorems/0875dcbb-a787-427b-bf28-9da761ff4ca2
-- title:
--   A truncated integer is the sum of its tail indicators
-- statement:
--   For natural numbers $m,R$, viewed as real numbers in the identity,
--   $$\min(m,R)=\sum_{j=0}^{R-1}\mathbf1_{\{j+1\leq m\}}.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/GaussDigits.lean#L121-L133

import Definitions.Def_BianchiIX_Statistics_GaussDigits
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
open scoped Topology ENNReal
open BianchiIX
noncomputable section

theorem BianchiIX.nat_min_eq_sum_tails (m R : ℕ) :
    min (m : ℝ) (R : ℝ) = ∑ j ∈ Finset.range R, if j + 1 ≤ m then (1 : ℝ) else 0 := by sorry
