-- Prove2me | Theorems.Thm_BianchiIX_InverseBranchTree_code_map_le_of_cell_bounds
-- name    : BianchiIX.InverseBranchTree.code_map_le_of_cell_bounds
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T18:46:29.628699+00:00
-- url     : https://prove2.me/theorems/9e0420f0-b60e-44d7-8b60-d63b797cd0c9
-- title:
--   Domination of the coded measure from cell bounds
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
--
--   Let $S=\bigcap_nS_n$ be the surviving set. For $x\in S$, denote its unique
--   length-$n$ cell word by $v_n(x)$ and define $a_n(x)$ by
--   $v_{n+1}(x)=v_n(x)a_n(x)$. Let $g_b(t)=1/(b+t)$ and
--   $G_v=g_{v_0}\circ\cdots\circ g_{v_{|v|-1}}$, with the empty composition the
--   identity. The code is
--   $$\kappa(x)=\lim_{n\to\infty}G_{v_n(x)}(0).$$
--   For a Borel measure $\mu$ on $\mathbb R$, write $\mu_S$ for its pullback
--   to the measurable subtype $S$ by the inclusion into $\mathbb R$.
--   Let $\mu,\nu$ be Borel measures on $\mathbb R$,
--   with $\nu$ outer regular. If $C\geq0$ is finite and
--   $$\mu(C_v)\leq C\nu(G_v((0,1)))$$
--   for every nonempty positive-digit word $v$, then
--   $$\kappa_*\mu_S\leq C\nu.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/TreeCoding.lean#L120-L134

import Definitions.Def_BianchiIX_Statistics_GaussCylinders
import Definitions.Def_BianchiIX_Statistics_TreeCoding
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
open BianchiIX.InverseBranchTree
variable (T : InverseBranchTree)

theorem BianchiIX.InverseBranchTree.code_map_le_of_cell_bounds (μ ν : Measure ℝ) [ν.OuterRegular] (C : ℝ≥0)
    (hbound : ∀ w : List ℕ+, w ≠ [] →
      μ (T.cell w) ≤ (C : ℝ≥0∞) * ν (gaussCylinder (w.map (fun a : ℕ+ => (a : ℕ))))) :
    Measure.map T.code (μ.comap (Subtype.val : T.survivors → ℝ)) ≤ C • ν := by sorry
