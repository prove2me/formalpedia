-- Prove2me | Theorems.Thm_BianchiIX_gaussCode_map_le_smul_of_cylinder_bounds
-- name    : BianchiIX.gaussCode_map_le_smul_of_cylinder_bounds
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T16:03:22.859481+00:00
-- url     : https://prove2.me/theorems/ab69935a-0e30-46ab-8562-038786fe3e17
-- title:
--   Uniform cylinder bounds give measure domination with the same constant
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
--   Let $(X,\Sigma,\mu)$ be a measure space, let $\nu$ be a Borel measure on
--   $\mathbb R$, and let $a:X\to A^{\mathbb N}$. For a word $w$, put
--   $$E_w=\{x\in X:a(x)|_{|w|}=w\},\qquad f=\pi\circ a.$$
--
--   Suppose $\nu$ is outer regular, $a$ is measurable, and $C\geq0$ is a real constant.
--   If $\mu(E_w)\leq C\nu(C(w))$ for every nonempty positive-digit word $w$,
--   then $f_*\mu\leq C\nu$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/GaussCylinders.lean#L198-L206

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
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Measure.Regular

open BianchiIX
noncomputable section
open Filter Set MeasureTheory
open scoped Topology ENNReal NNReal

theorem BianchiIX.gaussCode_map_le_smul_of_cylinder_bounds {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (ν : Measure ℝ) [ν.OuterRegular] (a : X → ℕ → ℕ+)
    (ha : Measurable a) (C : ℝ≥0)
    (hbound : ∀ w : List ℕ, w ≠ [] → (∀ k ∈ w, 1 ≤ k) →
      μ {x | digitPrefix (a x) w.length = w} ≤ (C : ℝ≥0∞) * ν (gaussCylinder w)) :
    Measure.map (gaussCode ∘ a) μ ≤ C • ν := by sorry
