-- Prove2me | Theorems.Thm_BianchiIX_exists_era_budget_threshold
-- name    : BianchiIX.exists_era_budget_threshold
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T20:07:35.105454+00:00
-- url     : https://prove2.me/theorems/65168962-2421-4a2a-8ba5-88b5a35938cc
-- title:
--   One amplitude threshold for all era budgets
-- statement:
--   Given $\eta>0$ and $C_v,C_i,C\geq0$, there exists
--   $0<B_{\max}<1$ such that for every $0<B\leq B_{\max}$,
--   $$B^\eta<1/160,\qquad
--   2C_i\sqrt B+4C_vB^{4/3}\leq\log2,\qquad
--   \tfrac{25}{16}CB^{17/30}\leq1.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/EraBudget.lean#L14-L40

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

theorem BianchiIX.exists_era_budget_threshold {η Cv Ci C : ℝ} (hη : 0 < η)
    (hCv : 0 ≤ Cv) (hCi : 0 ≤ Ci) (hC : 0 ≤ C) :
    ∃ Bmax : ℝ, 0 < Bmax ∧ Bmax < 1 ∧ ∀ B ∈ Ioc 0 Bmax,
      B ^ η < 1 / 160 ∧
        2 * Ci * Real.sqrt B + 4 * Cv * B ^ (4 / 3 : ℝ) ≤ Real.log 2 ∧
        (25 / 16 : ℝ) * C * B ^ (17 / 30 : ℝ) ≤ 1 := by sorry
