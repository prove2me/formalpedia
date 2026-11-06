-- Prove2me | Theorems.Thm_BianchiIX_stopped_layer_mass_le
-- name    : BianchiIX.stopped_layer_mass_le
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T17:18:39.306699+00:00
-- url     : https://prove2.me/theorems/2383fa39-d084-445f-8faa-169d8102c4cc
-- title:
--   Measure bound for a stopped layer
-- statement:
--   Let $a=(a_j)_{j\geq0}$ be positive integers and write
--   $g_b(x)=1/(b+x)$ and $G_n=g_{a_0}\circ\cdots\circ g_{a_{n-1}}$, with $G_0$ the identity.
--   Define $q_{-1}=0$, $q_0=1$, and $q_{n+1}=a_nq_n+q_{n-1}$. Set
--   $$Q_n(x)=q_n+q_{n-1}x,\qquad L_n(x)=-2\log Q_n(x).$$
--
--   Write $C_n=G_n((0,1))$ and
--   $$\ell_n=\frac1{q_n(q_n+q_{n-1})}.$$
--   Let $\lambda$ denote Lebesgue measure on $\mathbb R$.
--
--   Fix $n\geq0$ and a countable family of positive-digit sequences $a^i$ whose
--   prefixes of length $n$ are distinct. Write $G^i_n$ and $C^i_n$ for their
--   inverse prefixes and cylinders. Let $A_i\subset(0,1)$ be Borel and let $H_i$
--   be differentiable at every point of $A_i$ and injective there. Suppose that,
--   for some $L\in\mathbb R$ and $\ell\in[0,\infty]$,
--   $$\lambda(A_i)\leq\ell,\qquad |H_i'(x)|\leq e^L|(G^i_n)'(x)|
--   \quad(x\in A_i).$$
--   Then
--   $$\lambda\left(\bigcup_iH_i(A_i)\right)\leq2e^L\ell.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/StoppedMass.lean#L88-L109

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

theorem BianchiIX.stopped_layer_mass_le {ι : Type*} [Countable ι]
    (a : ι → ℕ → ℕ+) (n : ℕ) (H : ι → ℝ → ℝ) (A : ι → Set ℝ)
    {L : ℝ} {ell : ℝ≥0∞}
    (hunique : Function.Injective (fun i => digitPrefix (a i) n))
    (hA : ∀ i, MeasurableSet (A i)) (hAsub : ∀ i, A i ⊆ Ioo (0 : ℝ) 1)
    (hH : ∀ i, ∀ x ∈ A i, DifferentiableAt ℝ (H i) x) (hinj : ∀ i, InjOn (H i) (A i))
    (hsize : ∀ i, volume (A i) ≤ ell)
    (hbound : ∀ i, ∀ x ∈ A i,
      |deriv (H i) x| ≤ Real.exp L * |deriv (gaussWord (digitPrefix (a i) n)) x|) :
    volume (stoppedLayer H A) ≤ 2 * ENNReal.ofReal (Real.exp L) * ell := by sorry
