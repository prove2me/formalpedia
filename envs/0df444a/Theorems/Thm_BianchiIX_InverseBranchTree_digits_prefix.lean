-- Prove2me | Theorems.Thm_BianchiIX_InverseBranchTree_digits_prefix
-- name    : BianchiIX.InverseBranchTree.digits_prefix
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T18:41:27.629712+00:00
-- url     : https://prove2.me/theorems/93fab39d-cff7-49d1-bd98-a6a8136c58e8
-- title:
--   Digit prefixes coincide with the chosen cell words
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
--   The length-$n$ prefix of $(a_j(x))_{j\geq0}$
--   is $v_n(x)$, after identifying positive integers with natural numbers.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/TreeCoding.lean#L57-L65

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

theorem BianchiIX.InverseBranchTree.digits_prefix (x : T.survivors) (n : ℕ) :
    digitPrefix (T.digits x) n = (T.word x n).map (fun a : ℕ+ => (a : ℕ)) := by sorry
