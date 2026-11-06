-- Prove2me | Theorems.Thm_BianchiIX_InverseBranchTree_cell_volume_le
-- name    : BianchiIX.InverseBranchTree.cell_volume_le
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T17:56:25.972336+00:00
-- url     : https://prove2.me/theorems/9c8ef78a-ff0f-4019-b53a-f8b950789c91
-- title:
--   Cell length from a root-map derivative comparison
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
--   Fix a word $v$ and $L\in\mathbb R$. Suppose
--   $K_v\subset(0,1)$, $H_v$ is differentiable there, and
--   $|H_v'(t)|\leq e^L|G_v'(t)|$ for $t\in K_v$. Then
--   $$\lambda(C_v)\leq e^L\lambda(G_v((0,1))),$$
--   where $\lambda$ is Lebesgue measure.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/TreeMeasure.lean#L32-L42

import Definitions.Def_BianchiIX_Statistics_GaussInverse
import Definitions.Def_BianchiIX_Statistics_GaussCoding
import Definitions.Def_BianchiIX_Statistics_GaussCylinders
import Definitions.Def_BianchiIX_Statistics_BranchTree
import Definitions.Def_BianchiIX_Statistics_TreeMeasure
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

theorem BianchiIX.InverseBranchTree.cell_volume_le (w : List ℕ+) {L : ℝ}
    (hK : T.terminal w ⊆ Ioo (0 : ℝ) 1)
    (hF : ∀ x ∈ T.terminal w, DifferentiableAt ℝ (T.toRoot w) x)
    (hbound : ∀ x ∈ T.terminal w, |deriv (T.toRoot w) x| ≤
      Real.exp L * |deriv (gaussWord (w.map (fun a : ℕ+ => (a : ℕ)))) x|) :
    volume (T.cell w) ≤ ENNReal.ofReal (Real.exp L) *
      volume (gaussCylinder (w.map (fun a : ℕ+ => (a : ℕ)))) := by sorry
