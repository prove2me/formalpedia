-- Prove2me | Theorems.Thm_BianchiIX_gaussWord_image_measure_ge
-- name    : BianchiIX.gaussWord_image_measure_ge
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T16:45:19.573212+00:00
-- url     : https://prove2.me/theorems/58c62ebb-4141-4d8f-aae1-2ec5c7203bd7
-- title:
--   Lower image measure bound for every positive word
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
--   Let $\lambda$ be Lebesgue measure. For every finite
--   positive-digit word $v$ and Borel $A\subset(0,1)$,
--   $$\tfrac12\lambda(C(v))\lambda(A)\leq\lambda(G_v(A)).$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/GaussErgodic.lean#L31-L35

import Definitions.Def_BianchiIX_Statistics_GaussInverse
import Definitions.Def_BianchiIX_Statistics_GaussCoding
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
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Dynamics.Ergodic.Ergodic

open Set Filter MeasureTheory
open scoped ENNReal
open BianchiIX

theorem BianchiIX.gaussWord_image_measure_ge (w : List ℕ) (hw : ∀ k ∈ w, 1 ≤ k) {A : Set ℝ}
    (hA : MeasurableSet A) (hsub : A ⊆ Ioo (0 : ℝ) 1) :
    (1 / 2 : ℝ≥0∞) * volume (gaussCylinder w) * volume A ≤ volume (gaussWord w '' A) := by sorry
