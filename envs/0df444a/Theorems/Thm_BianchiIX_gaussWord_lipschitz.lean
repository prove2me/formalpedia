-- Prove2me | Theorems.Thm_BianchiIX_gaussWord_lipschitz
-- name    : BianchiIX.gaussWord_lipschitz
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T13:09:01.116168+00:00
-- url     : https://prove2.me/theorems/dd0199ed-75e3-42b9-a6c4-71247f96cd22
-- title:
--   Contraction of finite Gauss inverse compositions
-- statement:
--   Write $g_a(x)=1/(a+x)$. For a finite word
--   $w=(a_0,\ldots,a_{k-1})$ of natural numbers, let
--   $$G_w=g_{a_0}\circ\cdots\circ g_{a_{k-1}},\qquad G_{\varnothing}(x)=x.$$
--
--   If every digit in $w$ is at least $1$, then for all $x,y\geq0$,
--   $$|G_w(x)-G_w(y)|\leq4^{-\lfloor |w|/2\rfloor}|x-y|.$$
--   This yields contraction uniformly over positive digit words of a given length.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/GaussInverse.lean#L99-L118

import Definitions.Def_BianchiIX_Statistics_GaussInverse
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.List.Induction
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open BianchiIX
noncomputable section
open Filter
open scoped Topology

theorem BianchiIX.gaussWord_lipschitz (w : List ℕ) (hw : ∀ a ∈ w, 1 ≤ a)
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |gaussWord w x - gaussWord w y| ≤ (1 / 4 : ℝ) ^ (w.length / 2) * |x - y| := by sorry
