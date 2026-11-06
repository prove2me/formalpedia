-- Prove2me | Theorems.Thm_BianchiIX_gaussCylinder_prefixes_disjoint
-- name    : BianchiIX.gaussCylinder_prefixes_disjoint
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T17:03:43.93921+00:00
-- url     : https://prove2.me/theorems/ee071024-54f5-4275-8a9e-7641d09833a2
-- title:
--   Disjoint cylinders for distinct prefixes of equal length
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
--   Let $a^i$ be any family of positive-digit sequences.
--   If their prefixes of length $n$ are distinct, the cylinders $C(a^i|_n)$
--   are pairwise disjoint.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/StoppedMass.lean#L34-L46

import Definitions.Def_BianchiIX_Statistics_GaussCoding
import Definitions.Def_BianchiIX_Statistics_GaussCylinders
import Definitions.Def_BianchiIX_Statistics_StoppedMass
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

open BianchiIX
noncomputable section
open Set MeasureTheory
open scoped ENNReal

theorem BianchiIX.gaussCylinder_prefixes_disjoint {ι : Type*} (a : ι → ℕ → ℕ+) (n : ℕ)
    (hunique : Function.Injective (fun i => digitPrefix (a i) n)) :
    Pairwise (fun i j => Disjoint (gaussCylinder (digitPrefix (a i) n))
      (gaussCylinder (digitPrefix (a j) n))) := by sorry
