-- Prove2me | Theorems.Thm_BianchiIX_InverseBranchTree_root_sdiff_survivors
-- name    : BianchiIX.InverseBranchTree.root_sdiff_survivors
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T17:20:16.78952+00:00
-- url     : https://prove2.me/theorems/fde3ccb3-76b6-4508-a5a9-14d2b4cbfcdd
-- title:
--   Decomposition of all lost root points into stopped node images
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
--   One has
--   $$R\setminus\bigcap_{n\geq0}S_n
--   =\bigcup_{n\geq0}\bigcup_{|v|=n}H_v(D_v).$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/BranchTree.lean#L212-L216

import Definitions.Def_BianchiIX_Statistics_StoppedMass
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

theorem BianchiIX.InverseBranchTree.root_sdiff_survivors :
    T.root \ survivingSet T.level =
      ⋃ n, ⋃ w : {w : List ℕ+ // w.length = n}, T.toRoot w.val '' T.stoppedDomain w.val := by sorry
