-- Prove2me | Theorems.Thm_BianchiIX_gaussInv_pair_lipschitz
-- name    : BianchiIX.gaussInv_pair_lipschitz
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T13:05:59.045745+00:00
-- url     : https://prove2.me/theorems/fc58b629-765f-4c79-8e57-915a8dd03a05
-- title:
--   Two inverse Gauss branches contract by one quarter
-- statement:
--   Write $g_a(x)=1/(a+x)$. For a finite word
--   $w=(a_0,\ldots,a_{k-1})$ of natural numbers, let
--   $$G_w=g_{a_0}\circ\cdots\circ g_{a_{k-1}},\qquad G_{\varnothing}(x)=x.$$
--
--   For real $a,b\geq1$ and $x,y\geq0$,
--   $$|g_a(g_b(x))-g_a(g_b(y))|\leq\tfrac14|x-y|.$$
--   The estimate is uniform in the two branch parameters.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/GaussInverse.lean#L66-L85

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

theorem BianchiIX.gaussInv_pair_lipschitz
    {a b x y : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |gaussInv a (gaussInv b x) - gaussInv a (gaussInv b y)| ≤ (1 / 4) * |x - y| := by sorry
