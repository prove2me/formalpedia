-- Prove2me | Theorems.Thm_BianchiIX_measurableEmbedding_gaussWord
-- name    : BianchiIX.measurableEmbedding_gaussWord
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T15:56:01.828294+00:00
-- url     : https://prove2.me/theorems/dfe8e493-888c-4293-b1ba-ce64710c2d2e
-- title:
--   Measurable embeddings defined by finite Gauss words
-- statement:
--   Let $A=\{1,2,3,\ldots\}$, and let $a=(a_0,a_1,\ldots)\in A^{\mathbb N}$.
--   For $b\in A$, write $g_b(x)=1/(b+x)$. For a finite word $w=(b_0,\ldots,b_{n-1})$,
--   set $G_w=g_{b_0}\circ\cdots\circ g_{b_{n-1}}$, with $G_{\varnothing}$ the identity.
--   Define
--   $$q_n(a)=G_{(a_0,\ldots,a_{n-1})}(0),\qquad
--   \pi(a)=\lim_{n\to\infty}q_n(a),\qquad (\sigma^m a)_j=a_{m+j}.$$
--   The limit exists by the uniform contraction of inverse words. Write
--   $T(x)=1/x-\lfloor1/x\rfloor$ for $x\ne0$ and $T(0)=0$.
--
--   For a finite word $w$ of nonnegative integers, let
--   $$C(w)=G_w((0,1)).$$
--   For these maps on all of $\mathbb R$, the reciprocal uses $0^{-1}=0$.
--   Write $a|_n=(a_0,\ldots,a_{n-1})$. For a set $O\subset\mathbb R$, let
--   $\mathcal F(O)$ consist of the nonempty positive-digit words $w$ such that
--   $C(w)\subset O$ and no proper nonempty prefix $v$ has $C(v)\subset O$.
--
--   For every finite word $w$ of nonnegative integers, $G_w:\mathbb R\to\mathbb R$
--   is a measurable embedding.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/GaussCylinders.lean#L23-L26

import Definitions.Def_BianchiIX_Statistics_GaussCylinders
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
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Measure.Regular

open BianchiIX
noncomputable section
open Filter Set MeasureTheory
open scoped Topology ENNReal NNReal

theorem BianchiIX.measurableEmbedding_gaussWord (w : List ℕ) : MeasurableEmbedding (gaussWord w) := by sorry
