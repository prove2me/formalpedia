-- Prove2me | Theorems.Thm_BianchiIX_log_deriv_gaussWord_lipschitz
-- name    : BianchiIX.log_deriv_gaussWord_lipschitz
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T17:54:06.819164+00:00
-- url     : https://prove2.me/theorems/ceba5a62-5ea8-4e8a-9537-c1e83cf5c53e
-- title:
--   Lipschitz bound for the logarithmic derivative of a positive word
-- statement:
--   Write $g_a(x)=1/(a+x)$. For a finite word
--   $w=(a_0,\ldots,a_{k-1})$ of natural numbers, let
--   $$G_w=g_{a_0}\circ\cdots\circ g_{a_{k-1}},\qquad G_{\varnothing}(x)=x.$$
--   For any positive-digit word $v$ and $x,y\geq0$,
--   $$|\log|G_v'(x)|-\log|G_v'(y)||\leq2|x-y|.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/TreeDistortion.lean#L18-L23

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

theorem BianchiIX.log_deriv_gaussWord_lipschitz (w : List ℕ+) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |Real.log (|deriv (gaussWord (w.map (fun a : ℕ+ => (a : ℕ)))) x|) -
      Real.log (|deriv (gaussWord (w.map (fun a : ℕ+ => (a : ℕ)))) y|)| ≤ 2 * |x - y| := by sorry
