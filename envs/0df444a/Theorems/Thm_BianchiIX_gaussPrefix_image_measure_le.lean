-- Prove2me | Theorems.Thm_BianchiIX_gaussPrefix_image_measure_le
-- name    : BianchiIX.gaussPrefix_image_measure_le
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T16:27:07.009838+00:00
-- url     : https://prove2.me/theorems/b39a82a0-8aea-4a9d-8f78-36bf464f86ea
-- title:
--   Measure comparison with a Gauss inverse prefix
-- statement:
--   Let $a=(a_j)_{j\geq0}$ be positive integers and write
--   $g_b(x)=1/(b+x)$ and $G_n=g_{a_0}\circ\cdots\circ g_{a_{n-1}}$, with $G_0$ the identity.
--   Define $q_{-1}=0$, $q_0=1$, and $q_{n+1}=a_nq_n+q_{n-1}$. Set
--   $$Q_n(x)=q_n+q_{n-1}x,\qquad L_n(x)=-2\log Q_n(x).$$
--
--   Let $A\subset[0,\infty)$ be Borel measurable, and let $F$ be differentiable
--   at every point of $A$ and injective on $A$. If $L\in\mathbb R$ and
--   $|F'(x)|\leq e^L|G'_n(x)|$ on $A$, then
--   $$\lambda(F(A))\leq e^L\lambda(G_n(A)).$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/GaussTransport.lean#L37-L46

import Definitions.Def_BianchiIX_Statistics_GaussInverse
import Definitions.Def_BianchiIX_Statistics_GaussCoding
import Definitions.Def_BianchiIX_Statistics_GaussDistortion
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

theorem BianchiIX.gaussPrefix_image_measure_le (a : ℕ → ℕ+) (n : ℕ) {F : ℝ → ℝ}
    {A : Set ℝ} {L : ℝ} (hA : MeasurableSet A) (hApos : ∀ x ∈ A, 0 ≤ x)
    (hF : ∀ x ∈ A, DifferentiableAt ℝ F x) (hinj : InjOn F A)
    (hbound : ∀ x ∈ A, |deriv F x| ≤
      Real.exp L * |deriv (gaussWord (digitPrefix a n)) x|) :
    volume (F '' A) ≤ ENNReal.ofReal (Real.exp L) *
      volume (gaussWord (digitPrefix a n) '' A) := by sorry
