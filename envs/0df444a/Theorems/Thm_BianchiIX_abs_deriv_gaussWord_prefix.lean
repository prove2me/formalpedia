-- Prove2me | Theorems.Thm_BianchiIX_abs_deriv_gaussWord_prefix
-- name    : BianchiIX.abs_deriv_gaussWord_prefix
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T16:24:59.679736+00:00
-- url     : https://prove2.me/theorems/31a1d45a-7386-4a17-b356-f1a3937f472c
-- title:
--   Absolute derivative of a Gauss inverse prefix
-- statement:
--   Let $a=(a_j)_{j\geq0}$ be positive integers and write
--   $g_b(x)=1/(b+x)$ and $G_n=g_{a_0}\circ\cdots\circ g_{a_{n-1}}$, with $G_0$ the identity.
--   Define $q_{-1}=0$, $q_0=1$, and $q_{n+1}=a_nq_n+q_{n-1}$. Set
--   $$Q_n(x)=q_n+q_{n-1}x,\qquad L_n(x)=-2\log Q_n(x).$$
--   For $n\geq0$ and $x\geq0$,
--   $$|G'_n(x)|=\frac1{Q_n(x)^2}.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/GaussDistortion.lean#L73-L76

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

open BianchiIX
noncomputable section
open Set Finset

theorem BianchiIX.abs_deriv_gaussWord_prefix (a : ℕ → ℕ+) (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    |deriv (gaussWord (digitPrefix a n)) x| = 1 / (gaussDenom a n x) ^ 2 := by sorry
