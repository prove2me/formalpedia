-- Prove2me | Theorems.Thm_BianchiIX_gaussPrefix_small_set_image_le
-- name    : BianchiIX.gaussPrefix_small_set_image_le
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T16:43:30.616692+00:00
-- url     : https://prove2.me/theorems/50fe4258-c69f-483a-b6e1-87fcacc552fc
-- title:
--   Upper image measure bound relative to cylinder length
-- statement:
--   Let $a=(a_j)_{j\geq0}$ be positive integers and write
--   $g_b(x)=1/(b+x)$ and $G_n=g_{a_0}\circ\cdots\circ g_{a_{n-1}}$, with $G_0$ the identity.
--   Define $q_{-1}=0$, $q_0=1$, and $q_{n+1}=a_nq_n+q_{n-1}$. Set
--   $$Q_n(x)=q_n+q_{n-1}x,\qquad L_n(x)=-2\log Q_n(x).$$
--
--   Write $C_n=G_n((0,1))$ and
--   $$\ell_n=\frac1{q_n(q_n+q_{n-1})}.$$
--   Let $\lambda$ denote Lebesgue measure on $\mathbb R$.
--   For every Borel $A\subset(0,1)$,
--   $$\lambda(G_n(A))\leq2\lambda(C_n)\lambda(A).$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/GaussDensity.lean#L107-L124

import Definitions.Def_BianchiIX_Statistics_GaussInverse
import Definitions.Def_BianchiIX_Statistics_GaussCoding
import Definitions.Def_BianchiIX_Statistics_GaussCylinders
import Definitions.Def_BianchiIX_Statistics_GaussDensity
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

theorem BianchiIX.gaussPrefix_small_set_image_le (a : ℕ → ℕ+) (n : ℕ) {A : Set ℝ}
    (hA : MeasurableSet A) (hAsub : A ⊆ Ioo (0 : ℝ) 1) :
    volume (gaussWord (digitPrefix a n) '' A) ≤
      2 * volume (gaussCylinder (digitPrefix a n)) * volume A := by sorry
