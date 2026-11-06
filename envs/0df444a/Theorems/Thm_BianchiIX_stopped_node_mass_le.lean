-- Prove2me | Theorems.Thm_BianchiIX_stopped_node_mass_le
-- name    : BianchiIX.stopped_node_mass_le
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T17:15:05.364546+00:00
-- url     : https://prove2.me/theorems/70756b81-bea4-4872-907d-83c7386923da
-- title:
--   Measure bound for one stopped branch
-- statement:
--   Let $a=(a_j)_{j\geq0}$ be positive integers and write
--   $g_b(x)=1/(b+x)$ and $G_n=g_{a_0}\circ\cdots\circ g_{a_{n-1}}$, with $G_0$ the identity.
--   Define $q_{-1}=0$, $q_0=1$, and $q_{n+1}=a_nq_n+q_{n-1}$. Set
--   $$Q_n(x)=q_n+q_{n-1}x,\qquad L_n(x)=-2\log Q_n(x).$$
--
--   Write $C_n=G_n((0,1))$ and
--   $$\ell_n=\frac1{q_n(q_n+q_{n-1})}.$$
--   Let $\lambda$ denote Lebesgue measure on $\mathbb R$.
--   Let $A\subset(0,1)$ be Borel and let $H$
--   be differentiable on $A$ and injective there. If $L\in\mathbb R$,
--   $\ell\in[0,\infty]$, $\lambda(A)\leq\ell$, and
--   $|H'(x)|\leq e^L|G_n'(x)|$ on $A$, then
--   $$\lambda(H(A))\leq2e^L\ell\,\lambda(C_n).$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/StoppedMass.lean#L72-L86

import Definitions.Def_BianchiIX_Statistics_GaussInverse
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

theorem BianchiIX.stopped_node_mass_le (a : ℕ → ℕ+) (n : ℕ) {H : ℝ → ℝ}
    {A : Set ℝ} {L : ℝ} {ell : ℝ≥0∞} (hA : MeasurableSet A) (hAsub : A ⊆ Ioo (0 : ℝ) 1)
    (hH : ∀ x ∈ A, DifferentiableAt ℝ H x) (hinj : InjOn H A) (hsize : volume A ≤ ell)
    (hbound : ∀ x ∈ A, |deriv H x| ≤ Real.exp L * |deriv (gaussWord (digitPrefix a n)) x|) :
    volume (H '' A) ≤ (2 * ENNReal.ofReal (Real.exp L) * ell) *
      volume (gaussCylinder (digitPrefix a n)) := by sorry
