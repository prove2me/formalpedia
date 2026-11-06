-- Prove2me | Theorems.Thm_BianchiIX_stopped_total_mass_le
-- name    : BianchiIX.stopped_total_mass_le
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T17:21:26.075179+00:00
-- url     : https://prove2.me/theorems/5f52942a-164f-4a49-b017-85dd76505f41
-- title:
--   Measure bound for all stopping layers
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
--   Suppose such data are given for every depth
--   $n$, with its own countable index set, maps $H_{n,i}$, domains $A_{n,i}$,
--   sequences $a^{n,i}$, and size bound $\ell_n\in[0,\infty]$, while $L$ is
--   common to all depths. Then
--   $$\lambda\left(\bigcup_{n\geq0}\bigcup_iH_{n,i}(A_{n,i})\right)
--   \leq2e^L\sum_{n\geq0}\ell_n.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/StoppedMass.lean#L111-L128

import Definitions.Def_BianchiIX_Statistics_GaussInverse
import Definitions.Def_BianchiIX_Statistics_GaussCoding
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

theorem BianchiIX.stopped_total_mass_le {ι : ℕ → Type*} [∀ m, Countable (ι m)]
    (a : ∀ m, ι m → ℕ → ℕ+) (H : ∀ m, ι m → ℝ → ℝ) (A : ∀ m, ι m → Set ℝ)
    (ell : ℕ → ℝ≥0∞) (L : ℝ)
    (hunique : ∀ m, Function.Injective (fun i => digitPrefix (a m i) m))
    (hA : ∀ m i, MeasurableSet (A m i)) (hAsub : ∀ m i, A m i ⊆ Ioo (0 : ℝ) 1)
    (hH : ∀ m i, ∀ x ∈ A m i, DifferentiableAt ℝ (H m i) x)
    (hinj : ∀ m i, InjOn (H m i) (A m i)) (hsize : ∀ m i, volume (A m i) ≤ ell m)
    (hbound : ∀ m i, ∀ x ∈ A m i,
      |deriv (H m i) x| ≤ Real.exp L * |deriv (gaussWord (digitPrefix (a m i) m)) x|) :
    volume (⋃ m, stoppedLayer (H m) (A m)) ≤
      2 * ENNReal.ofReal (Real.exp L) * ∑' m, ell m := by sorry
