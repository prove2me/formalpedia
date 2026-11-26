-- Prove2me | Theorems.Thm_BBAssertion
-- name    : BBAssertion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:10:55.027505+00:00
-- url     : https://prove2.me/theorems/92081b1a-3602-458a-85eb-ae14e338b26d
-- title:
--   BBAssertion: BBAssertion
-- statement:
--   Theorem 4.4 (paper.tex 1218-1226, target `bbassertion`): for a complete, separable, geodesic
--   metric space `E` and a metric `1`-current `T` (`\noderef{MetricCurrent1}`) with `T ≠ 0` and
--   `∂T = 0` (`\noderef{BoundaryZero}`), there is a sequence `n l → ∞` of positive integers and a
--   doubly-indexed family of oriented, closed, piecewise-geodesic curves `ghat l i`
--   (`\noderef{IsClosedCurve}`, `\noderef{IsPiecewiseGeodesic}`) with `𝕄([[ghat l i]]) ≤
--   len(ghat l i) ≤ 2l` for every `l ≥ 1` and `i < n l`, such that eq.~closed1 holds for every `1`-form
--   `ω` and eq.~closed2's mass half and length half both converge to `1`. Assembled from
--   `\noderef{PaoliniStepanovExists}` (mass-realizing family `F`), `\noderef{MassPosOfNonzero}`
--   (nonvanishing of `F`'s mass measure), `\noderef{DiagonalizationGeneral}` (the countable family
--   `om` and its every-form upgrade), `\noderef{BBSamplingDiagonal}` (the diagonal curve family `γ`),
--   and `\noderef{ClosingUp}` (closing `γ` into loops `ghat`/`gbar`); the mass half of eq.~closed2 uses
--   `\noderef{MassSupFormula}`, `\noderef{MassFamilyBound}`, and `\noderef{EasyEstimateForMass}`
--   sandwiched against `\noderef{MetricCurrent1}`'s `finiteMass` field. `[Nonempty E]` is required
--   since the conclusion asserts the existence of curves and `Curve E` is uninhabited exactly when `E`
--   is.
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/BBAssertion.lean#L35-L243
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/BBAssertion.lean#L35-L243

import Definitions.Def_Tablet_MetricCurrent1
import Definitions.Def_Tablet_PSFamily
import Definitions.Def_Tablet_PaoliniStepanovExists
import Definitions.Def_Tablet_BoundaryZero
import Definitions.Def_Tablet_GeodesicPairing
import Definitions.Def_Tablet_BBSamplingDiagonal
import Definitions.Def_Tablet_DiagonalizationGeneral
import Definitions.Def_Tablet_ClosingUp
import Definitions.Def_Tablet_MassSupFormula
import Definitions.Def_Tablet_MassFamilyBound
import Definitions.Def_Tablet_MassPosOfNonzero
import Definitions.Def_Tablet_EasyEstimateForMass
import Definitions.Def_Tablet_IsClosedCurve
import Definitions.Def_Tablet_IsPiecewiseGeodesic
import Definitions.Def_Tablet_curveCurrent
import Definitions.Def_Tablet_BBAssertion
import Theorems.Thm_BBSamplingDiagonal
import Theorems.Thm_ClosingUp
import Theorems.Thm_DiagonalizationGeneral
import Theorems.Thm_EasyEstimateForMass
import Theorems.Thm_MassFamilyBound
import Theorems.Thm_MassPosOfNonzero

set_option autoImplicit false
open Set Filter Finset MeasureTheory ENNReal

theorem BBAssertion {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [CompleteSpace E] [TopologicalSpace.SeparableSpace E] [Nonempty E]
    (hAK : MassSupFormulaStatement E) (hPS : PaoliniStepanovExistsStatement E)
    (GP : GeodesicPairing E)
    (T : MetricCurrent1 E) (hT0 : T.toFun ≠ 0) (hbdry : BoundaryZero T.toFun) :
    ∃ (n : ℕ → ℕ) (ghat : ℕ → ℕ → Curve E),
      (∀ l : ℕ, 0 < n l) ∧ Tendsto n atTop atTop ∧
      (∀ l : ℕ, 1 ≤ l → ∀ i < n l, IsClosedCurve (ghat l i)) ∧
      (∀ l : ℕ, 1 ≤ l → ∀ i < n l, IsPiecewiseGeodesic (ghat l i)) ∧
      (∀ l : ℕ, 1 ≤ l → ∀ i < n l,
        massOfFunctional (curveCurrent (ghat l i)) ≤ ENNReal.ofReal (ghat l i).len) ∧
      (∀ l : ℕ, 1 ≤ l → ∀ i < n l, (ghat l i).len ≤ 2 * (l : ℝ)) ∧
      (∀ ω : Form1 E, Tendsto (fun l : ℕ =>
          (massOfFunctional T.toFun).toReal / ((n l : ℝ) * l) *
            ∑ i ∈ Finset.range (n l), curveCurrent (ghat l i) ω)
          atTop (nhds (T.toFun ω))) ∧
      (Tendsto (fun l : ℕ => (1 / ((n l : ℝ) * l)) *
          ∑ i ∈ Finset.range (n l), (massOfFunctional (curveCurrent (ghat l i))).toReal)
        atTop (nhds 1)) ∧
      (Tendsto (fun l : ℕ => (1 / ((n l : ℝ) * l)) *
          ∑ i ∈ Finset.range (n l), (ghat l i).len)
        atTop (nhds 1)) := by sorry
