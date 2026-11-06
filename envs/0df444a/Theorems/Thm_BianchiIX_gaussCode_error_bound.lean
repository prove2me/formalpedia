-- Prove2me | Theorems.Thm_BianchiIX_gaussCode_error_bound
-- name    : BianchiIX.gaussCode_error_bound
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T14:51:10.435075+00:00
-- url     : https://prove2.me/theorems/99dc2930-6bf8-4d55-ad04-c0e1f82e1377
-- title:
--   Error bound relative to the code of prescribed digits
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
--   For a real sequence $y=(y_m)_{m\geq0}$, define its local inverse recurrence error by
--   $$e_m=\left|y_m-\frac1{a_m+y_{m+1}}\right|.$$
--
--   Suppose $y_m\in[0,1]$ for every $m$. Then
--   $$|y_m-\pi(\sigma^m a)|\leq
--   \sum_{j=0}^{\infty}4^{-j}(e_{m+2j}+e_{m+2j+1})\qquad(m\in\mathbb N).$$
--   The exact comparison sequence is determined by the prescribed digits.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/GaussCoding.lean#L252-L259

import Definitions.Def_BianchiIX_Statistics_GaussCoding
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

open BianchiIX
noncomputable section
open Filter Set
open scoped Topology

theorem BianchiIX.gaussCode_error_bound (a : ℕ → ℕ+) {y : ℕ → ℝ}
    (hy : ∀ m, y m ∈ Icc (0 : ℝ) 1) (m : ℕ) :
    |y m - gaussCode (shiftDigits a m)| ≤ ∑' j : ℕ, (1 / 4 : ℝ) ^ j *
      (inverseError (fun k => (a k : ℕ)) y (m + 2 * j) +
        inverseError (fun k => (a k : ℕ)) y (m + 2 * j + 1)) := by sorry
