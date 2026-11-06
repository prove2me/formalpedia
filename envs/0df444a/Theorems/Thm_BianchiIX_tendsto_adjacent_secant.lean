-- Prove2me | Theorems.Thm_BianchiIX_tendsto_adjacent_secant
-- name    : BianchiIX.tendsto_adjacent_secant
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T20:30:41.375571+00:00
-- url     : https://prove2.me/theorems/c64b550a-f5ec-4070-a9d4-ddbfb948df1b
-- title:
--   Recovery of a within-derivative from adjacent secants
-- statement:
--   Suppose $f$ has derivative $d$ within $S\subset\mathbb R$
--   at $x$. Let $h_n\to0$ with $h_n\ne0$ and $x+h_n,x+2h_n\in S$ for all $n$.
--   Then
--   $$\frac{f(x+2h_n)-f(x+h_n)}{h_n}\longrightarrow d.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/CurveMeasurability.lean#L13-L38

import Definitions.Def_BianchiIX_Analysis_CurveMeasurability
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology

theorem BianchiIX.tendsto_adjacent_secant {f : ℝ → ℝ} {d x : ℝ} {S : Set ℝ} {h : ℕ → ℝ}
    (hf : HasDerivWithinAt f d S x) (ht : Tendsto h atTop (𝓝 0))
    (hn : ∀ n, h n ≠ 0) (h₁ : ∀ n, x + h n ∈ S) (h₂ : ∀ n, x + 2 * h n ∈ S) :
    Tendsto (fun n => (f (x + 2 * h n) - f (x + h n)) / h n) atTop (𝓝 d) := by sorry
