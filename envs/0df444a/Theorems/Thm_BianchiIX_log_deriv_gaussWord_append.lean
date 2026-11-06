-- Prove2me | Theorems.Thm_BianchiIX_log_deriv_gaussWord_append
-- name    : BianchiIX.log_deriv_gaussWord_append
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T17:58:14.63892+00:00
-- url     : https://prove2.me/theorems/c4722148-09b1-4030-a82a-3cee3c1bc210
-- title:
--   Logarithmic derivative after appending a Gauss branch
-- statement:
--   Write $g_a(x)=1/(a+x)$. For a finite word
--   $w=(a_0,\ldots,a_{k-1})$ of natural numbers, let
--   $$G_w=g_{a_0}\circ\cdots\circ g_{a_{k-1}},\qquad G_{\varnothing}(x)=x.$$
--   For a positive-digit word $v$, a positive digit $a$,
--   and $x\geq0$,
--   $$\log|G_{va}'(x)|=\log|G_v'(g_a(x))|+\log|g_a'(x)|.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/TreeDistortion.lean#L25-L41

import Definitions.Def_BianchiIX_Statistics_GaussCoding
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

theorem BianchiIX.log_deriv_gaussWord_append (w : List ℕ+) (a : ℕ+) {x : ℝ} (hx : 0 ≤ x) :
    Real.log |deriv (gaussWord ((w ++ [a]).map (fun b : ℕ+ => (b : ℕ)))) x| =
      Real.log |deriv (gaussWord (w.map (fun b : ℕ+ => (b : ℕ)))) (gaussInv a x)| +
        Real.log |deriv (gaussInv a) x| := by sorry
