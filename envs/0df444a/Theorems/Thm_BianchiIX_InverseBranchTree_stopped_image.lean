-- Prove2me | Theorems.Thm_BianchiIX_InverseBranchTree_stopped_image
-- name    : BianchiIX.InverseBranchTree.stopped_image
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T17:12:00.325127+00:00
-- url     : https://prove2.me/theorems/cb12deea-30c9-41be-823c-9abcf4c36093
-- title:
--   The stopped image is a parent cell minus its children
-- statement:
--   Let $T$ be an inverse-branch tree with open root
--   $R\subset\mathbb R$. For every finite positive-digit word $v$ and digit $a$,
--   let $U_{v,a}\subset\mathbb R$ be open and let $h_{v,a}:\mathbb R\to\mathbb R$
--   be continuous and injective on $U_{v,a}$. For fixed $v$, assume the images
--   $h_{v,a}(U_{v,a})$ are pairwise disjoint. Define
--   $$K_\varnothing=R,\qquad K_{va}=U_{v,a}\cap h_{v,a}^{-1}(K_v),$$
--   $$H_\varnothing=\mathrm{id},\qquad H_{va}=H_v\circ h_{v,a},\qquad C_v=H_v(K_v),$$
--   $$D_v=K_v\setminus\bigcup_a h_{v,a}(U_{v,a}),\qquad S_n=\bigcup_{|v|=n}C_v.$$
--   Here $va$ denotes appending the digit $a$ to $v$.
--   For every word $v$,
--   $$H_v(D_v)=C_v\setminus\bigcup_aC_{va}.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/BranchTree.lean#L165-L184

import Definitions.Def_BianchiIX_Statistics_BranchTree
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
open BianchiIX
open BianchiIX.InverseBranchTree
variable (T : InverseBranchTree)

theorem BianchiIX.InverseBranchTree.stopped_image (w : List ℕ+) :
    T.toRoot w '' T.stoppedDomain w = T.cell w \ ⋃ a, T.cell (w ++ [a]) := by sorry
