-- Prove2me | Theorems.Thm_BianchiIX_gaussPrefix_density_bounds
-- name    : BianchiIX.gaussPrefix_density_bounds
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T16:41:49.491502+00:00
-- url     : https://prove2.me/theorems/9df87813-3448-4bfb-8883-61f7c9622a72
-- title:
--   Uniform two-sided bounds for the normalized cylinder density
-- statement:
--   Let $a=(a_j)_{j\geq0}$ be positive integers and write
--   $g_b(x)=1/(b+x)$ and $G_n=g_{a_0}\circ\cdots\circ g_{a_{n-1}}$, with $G_0$ the identity.
--   Define $q_{-1}=0$, $q_0=1$, and $q_{n+1}=a_nq_n+q_{n-1}$. Set
--   $$Q_n(x)=q_n+q_{n-1}x,\qquad L_n(x)=-2\log Q_n(x).$$
--
--   Write $C_n=G_n((0,1))$ and
--   $$\ell_n=\frac1{q_n(q_n+q_{n-1})}.$$
--   Let $\lambda$ denote Lebesgue measure on $\mathbb R$.
--   For $n\geq0$ and $x\in[0,1]$,
--   $$\tfrac12\ell_n\leq |G_n'(x)|\leq2\ell_n.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/GaussDensity.lean#L76-L105

import Definitions.Def_BianchiIX_Statistics_GaussInverse
import Definitions.Def_BianchiIX_Statistics_GaussCoding
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

theorem BianchiIX.gaussPrefix_density_bounds (a : ℕ → ℕ+) (n : ℕ)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    (1 / 2) * gaussPrefixLength a n ≤ |deriv (gaussWord (digitPrefix a n)) x| ∧
      |deriv (gaussWord (digitPrefix a n)) x| ≤ 2 * gaussPrefixLength a n := by sorry
