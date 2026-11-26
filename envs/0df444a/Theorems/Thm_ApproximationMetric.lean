-- Prove2me | Theorems.Thm_ApproximationMetric
-- name    : ApproximationMetric
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:47:27.753105+00:00
-- url     : https://prove2.me/theorems/95f38567-6340-47c6-94af-6126505aca7d
-- title:
--   Approximation Metric: Approximation Metric
-- statement:
--   Theorem 1.1 (paper.tex 267-279, target `approximationMetric`): for a complete, separable,
--   geodesic metric space `E`, a metric `1`-current `T` (`\noderef{MetricCurrent1}`) with `∂T = 0`
--   (`\noderef{BoundaryZero}`), and `0 < ε ≤ 1`, there exist doubly-indexed piecewise-geodesic
--   (`\noderef{IsPiecewiseGeodesic}`) closed (`\noderef{IsClosedCurve}`) curves `γ n i` and
--   nonnegative scalars `lam n i` such that the divided-current sums converge to `T(ω)` for every
--   `1`-form `ω` (eq.~limit, via `\noderef{curveCurrent}`), the scalars have uniformly bounded total
--   variation `(1+ε)·𝕄(T)` (eq.~mass), and every curve has Morrey norm at most `2088/ε²`
--   (eq.~morrey\_bound, via `\noderef{curveMeasure}` and `morreyNorm`). `C = 4·522 = 2088` is pinned
--   as a numeral (pm-0021): the paper quantifies `C` universally, outside `E`, so pinning a concrete
--   value is at least as strong as the paper's existential and is faithful to it. `[Nonempty E]` is
--   required, since the conclusion demands a total function `γ : ℕ → ℕ → Curve E` and `Curve E` is
--   uninhabited exactly when `E` is (`\noderef{Curve}`'s `toFun : ℝ → E` field), while nothing else in
--   the hypotheses forces `E` nonempty here (unlike `\noderef{BBAssertion}`, this theorem carries no
--   `T ≠ 0` hypothesis: the empty space with the zero current is a complete, separable, geodesic space
--   with `∂T = 0` and `𝕄(T) ≠ ⊤`, yet has no curves at all). Assembled from `\noderef{BBAssertion}`
--   (for the family `ghat`) and `\noderef{SurgeryEta}` (applied to each `ghat l i` at `η = ε/2`).
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/ApproximationMetric.lean#L33-L362
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/ApproximationMetric.lean#L33-L362

import Definitions.Def_Tablet_MetricCurrent1
import Definitions.Def_Tablet_BoundaryZero
import Definitions.Def_Tablet_GeodesicPairing
import Definitions.Def_Tablet_MassSupFormula
import Definitions.Def_Tablet_PaoliniStepanovExists
import Definitions.Def_Tablet_BBAssertion
import Definitions.Def_Tablet_SurgeryEta
import Definitions.Def_Tablet_IsClosedCurve
import Definitions.Def_Tablet_IsPiecewiseGeodesic
import Definitions.Def_Tablet_curveCurrent
import Definitions.Def_Tablet_curveMeasure
import Definitions.Def_Tablet_morreyNorm
import Definitions.Def_Tablet_ApproximationMetric
import Theorems.Thm_BBAssertion
import Theorems.Thm_SurgeryEta

set_option autoImplicit false
open Set Filter Finset MeasureTheory ENNReal

theorem ApproximationMetric {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [CompleteSpace E] [TopologicalSpace.SeparableSpace E] [Nonempty E]
    (hAK : MassSupFormulaStatement E) (hPS : PaoliniStepanovExistsStatement E)
    (GP : GeodesicPairing E)
    (T : MetricCurrent1 E) (hbdry : BoundaryZero T.toFun)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ (γ : ℕ → ℕ → Curve E) (lam : ℕ → ℕ → ℝ),
      (∀ n : ℕ, ∀ i < n, 0 ≤ lam n i) ∧
      (∀ n : ℕ, ∀ i < n, IsClosedCurve (γ n i)) ∧
      (∀ n : ℕ, ∀ i < n, IsPiecewiseGeodesic (γ n i)) ∧
      (∀ ω : Form1 E, Tendsto (fun n : ℕ =>
          ∑ i ∈ Finset.range n, lam n i * (curveCurrent (γ n i) ω / (γ n i).len))
        atTop (nhds (T.toFun ω))) ∧
      (∀ n : ℕ, ∑ i ∈ Finset.range n, |lam n i|
          ≤ (1 + ε) * (massOfFunctional T.toFun).toReal) ∧
      (∀ n : ℕ, ∀ i < n,
          morreyNorm (curveMeasure (γ n i)) ≤ ENNReal.ofReal (2088 / ε ^ 2)) := by sorry
