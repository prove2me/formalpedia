-- Prove2me | Theorems.Thm_BianchiIX_gaussDenoms_bounds
-- name    : BianchiIX.gaussDenoms_bounds
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T16:18:24.99504+00:00
-- url     : https://prove2.me/theorems/9ef4021b-25c4-4d3a-a417-919218a421ad
-- title:
--   Elementary bounds for continued-fraction continuants
-- statement:
--   Let $a=(a_j)_{j\geq0}$ be positive integers and write
--   $g_b(x)=1/(b+x)$ and $G_n=g_{a_0}\circ\cdots\circ g_{a_{n-1}}$, with $G_0$ the identity.
--   Define $q_{-1}=0$, $q_0=1$, and $q_{n+1}=a_nq_n+q_{n-1}$. Set
--   $$Q_n(x)=q_n+q_{n-1}x,\qquad L_n(x)=-2\log Q_n(x).$$
--   For every $n\geq0$,
--   $$q_n\geq1,\qquad 0\leq q_{n-1}\leq q_n.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/GaussDistortion.lean#L18-L28

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

theorem BianchiIX.gaussDenoms_bounds (a : ℕ → ℕ+) (n : ℕ) :
    1 ≤ (gaussDenoms a n).1 ∧ 0 ≤ (gaussDenoms a n).2 ∧
      (gaussDenoms a n).2 ≤ (gaussDenoms a n).1 := by sorry
