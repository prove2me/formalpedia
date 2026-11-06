-- Prove2me | Theorems.Thm_BianchiIX_gaussWord_positive_regular
-- name    : BianchiIX.gaussWord_positive_regular
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T17:52:38.430953+00:00
-- url     : https://prove2.me/theorems/ec628c19-4702-4d3e-8372-9215e77c5306
-- title:
--   Nonvanishing derivatives of positive Gauss words
-- statement:
--   Write $g_a(x)=1/(a+x)$. For a finite word
--   $w=(a_0,\ldots,a_{k-1})$ of natural numbers, let
--   $$G_w=g_{a_0}\circ\cdots\circ g_{a_{k-1}},\qquad G_{\varnothing}(x)=x.$$
--   If all digits of $v$ are positive and $x\geq0$, then
--   $G_v$ is differentiable at $x$ and $G_v'(x)\ne0$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/TreeDistortion.lean#L10-L16

import Definitions.Def_BianchiIX_Statistics_GaussCoding
import Definitions.Def_BianchiIX_Statistics_GaussDistortion
import Definitions.Def_BianchiIX_Statistics_TreeMeasure
import Definitions.Def_BianchiIX_Statistics_TreeDistortion
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

open Set MeasureTheory
open scoped NNReal ENNReal
open BianchiIX

theorem BianchiIX.gaussWord_positive_regular (w : List ℕ+) {x : ℝ} (hx : 0 ≤ x) :
    DifferentiableAt ℝ (gaussWord (w.map (fun a : ℕ+ => (a : ℕ)))) x ∧
      deriv (gaussWord (w.map (fun a : ℕ+ => (a : ℕ)))) x ≠ 0 := by sorry
