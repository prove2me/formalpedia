-- Prove2me | Theorems.Thm_BianchiIX_gaussPrefix_cylinder_measure_le
-- name    : BianchiIX.gaussPrefix_cylinder_measure_le
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T16:28:13.943576+00:00
-- url     : https://prove2.me/theorems/6048b5c7-affa-4845-a266-53cf5b1b1811
-- title:
--   Bounding an image measure by its Gauss cylinder
-- statement:
--   Let $a=(a_j)_{j\geq0}$ be positive integers and write
--   $g_b(x)=1/(b+x)$ and $G_n=g_{a_0}\circ\cdots\circ g_{a_{n-1}}$, with $G_0$ the identity.
--   Define $q_{-1}=0$, $q_0=1$, and $q_{n+1}=a_nq_n+q_{n-1}$. Set
--   $$Q_n(x)=q_n+q_{n-1}x,\qquad L_n(x)=-2\log Q_n(x).$$
--
--   Let $A\subset(0,1)$ be Borel measurable, and let $F$ be differentiable on $A$
--   and injective there. If $|F'(x)|\leq e^L|G'_n(x)|$ for all $x\in A$, then
--   $$\lambda(F(A))\leq e^L\lambda(G_n((0,1))).$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/GaussTransport.lean#L76-L84

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

open BianchiIX
noncomputable section
open Set Finset MeasureTheory
open scoped ENNReal

theorem BianchiIX.gaussPrefix_cylinder_measure_le (a : ℕ → ℕ+) (n : ℕ) {F : ℝ → ℝ}
    {A : Set ℝ} {L : ℝ} (hA : MeasurableSet A) (hAsub : A ⊆ Ioo (0 : ℝ) 1)
    (hF : ∀ x ∈ A, DifferentiableAt ℝ F x) (hinj : InjOn F A)
    (hbound : ∀ x ∈ A, |deriv F x| ≤
      Real.exp L * |deriv (gaussWord (digitPrefix a n)) x|) :
    volume (F '' A) ≤ ENNReal.ofReal (Real.exp L) *
      volume (gaussCylinder (digitPrefix a n)) := by sorry
