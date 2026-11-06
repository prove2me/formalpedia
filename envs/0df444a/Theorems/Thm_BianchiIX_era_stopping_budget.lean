-- Prove2me | Theorems.Thm_BianchiIX_era_stopping_budget
-- name    : BianchiIX.era_stopping_budget
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T20:14:56.830825+00:00
-- url     : https://prove2.me/theorems/21257c4b-eeb7-4848-a5aa-0143776da643
-- title:
--   The total stopping budget for era amplitudes
-- statement:
--   For $B\in\mathbb R$ and $m\in\mathbb N$, define
--   $$M_m(B)=B^{(4/3)^m},$$
--   where the outer power is the real power.
--   Suppose $0<B\leq1$, $\eta\geq0$, and
--   $B^\eta<1/160$. As an extended nonnegative series,
--   $$\sum_{m\geq0}10M_m(B)^\eta\leq20B^\eta.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/EraBudget.lean#L71-L83

import Definitions.Def_BianchiIX_Analysis_AmplitudeSequence
import Definitions.Def_BianchiIX_Statistics_EraBudget
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.Dynamics.BirkhoffSum.Average
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Data.List.Induction
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
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology ENNReal

theorem BianchiIX.era_stopping_budget {B η : ℝ} (hB : 0 < B) (hB1 : B ≤ 1)
    (hη : 0 ≤ η) (hsmall : B ^ η < 1 / 160) :
    (∑' m, ENNReal.ofReal (10 * eraAmplitude B m ^ η)) ≤ ENNReal.ofReal (20 * B ^ η) := by sorry
