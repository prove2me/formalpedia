-- Prove2me | Theorems.Thm_BianchiIX_coordinateFactor_identity
-- name    : BianchiIX.coordinateFactor_identity
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T23:07:04.52288+00:00
-- url     : https://prove2.me/theorems/4e4e9807-afef-49fe-8039-fbf649beec8b
-- title:
--   Factorization of a coordinate difference by its integral derivative
-- statement:
--   For $n\in\mathbb N$, $i\in\{0,\ldots,n-1\}$,
--   and $y\in\mathbb R^n$, define $\gamma_i(y,s)$ by replacing the $i$th
--   coordinate of $y$ by $sy_i$. Let $e_i$ be the $i$th coordinate unit vector.
--   For $f:\mathbb R^n\to\mathbb R$, define
--   $$\mathcal F_i[f](y)=\int_0^1 df_{\gamma_i(y,s)}(e_i)\,ds.$$
--   The derivative in this total definition is zero at points where $f$ is
--   not differentiable.
--   If $f$ is $C^2$ at $\gamma_i(y,s)$
--   for every $s\in[0,1]$, then
--   $$f(y)-f(y-y_i e_i)=y_i\mathcal F_i[f](y).$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/CoordinateFactor.lean#L46-L65

import Definitions.Def_BianchiIX_Analysis_CoordinateFactor
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Data.Fin.VecNotation
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

noncomputable section
open BianchiIX
open Set MeasureTheory

theorem BianchiIX.coordinateFactor_identity {n : ℕ} {f : (Fin n → ℝ) → ℝ} {i : Fin n} {Y : Fin n → ℝ}
    (hf : ∀ s ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 2 f (coordinateSegment i Y s)) :
    f Y - f (Function.update Y i 0) = Y i * coordinateFactor f i Y := by sorry
