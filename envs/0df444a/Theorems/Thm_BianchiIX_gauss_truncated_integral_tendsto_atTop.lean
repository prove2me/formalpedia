-- Prove2me | Theorems.Thm_BianchiIX_gauss_truncated_integral_tendsto_atTop
-- name    : BianchiIX.gauss_truncated_integral_tendsto_atTop
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T19:39:21.64078+00:00
-- url     : https://prove2.me/theorems/7798afa7-bf36-4104-97bd-2657ea5e7dfc
-- title:
--   Divergence of the truncated Gauss means
-- statement:
--   As $R\in\mathbb N$ tends to infinity,
--   $$\frac{\log(R+1)}{\log2}\longrightarrow+\infty.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/GaussDigitStatistics.lean#L82-L85

import Definitions.Def_BianchiIX_Statistics_GaussMeasure
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

theorem BianchiIX.gauss_truncated_integral_tendsto_atTop :
    Tendsto (fun R : ℕ => Real.log ((R : ℝ) + 1) / Real.log 2) atTop atTop := by sorry
