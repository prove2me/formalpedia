-- Prove2me | Theorems.Thm_BianchiIX_era_distortion_budget
-- name    : BianchiIX.era_distortion_budget
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T20:14:28.578515+00:00
-- url     : https://prove2.me/theorems/072025aa-6aa4-41e6-b4bb-5b30dc475708
-- title:
--   A summable distortion budget for era amplitudes
-- statement:
--   For $B\in\mathbb R$ and $m\in\mathbb N$, define
--   $$M_m(B)=B^{(4/3)^m},$$
--   where the outer power is the real power.
--   Suppose $0<B\leq1$, $0\leq\eta\leq1/2$,
--   $B^\eta<1/160$, and $C_v,C_i\geq0$. Both sequences
--   $C_vM_m(B)$ and $C_i\sqrt{M_m(B)}$ are summable, and for every $n$,
--   $$\sum_{j=0}^{n-1}\left(C_i\sqrt{M_j(B)}
--   +\mathbf1_{\{j\ne0\}}\,2C_vM_j(B)\right)
--   \leq2C_i\sqrt B+4C_vB^{4/3}.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/EraBudget.lean#L42-L69

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

theorem BianchiIX.era_distortion_budget {B η Cv Ci : ℝ} (hB : 0 < B) (hB1 : B ≤ 1)
    (hη : 0 ≤ η) (hηhalf : η ≤ 1 / 2) (hsmall : B ^ η < 1 / 160)
    (hCv : 0 ≤ Cv) (hCi : 0 ≤ Ci) :
    (Summable fun m => Cv * eraAmplitude B m) ∧
      (Summable fun m => Ci * Real.sqrt (eraAmplitude B m)) ∧
      ∀ n, (∑ j ∈ Finset.range n,
        (Ci * Real.sqrt (eraAmplitude B j) + if j = 0 then 0 else 2 * (Cv * eraAmplitude B j))) ≤
          2 * Ci * Real.sqrt B + 4 * Cv * B ^ (4 / 3 : ℝ) := by sorry
