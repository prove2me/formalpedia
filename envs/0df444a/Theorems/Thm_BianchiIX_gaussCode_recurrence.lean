-- Prove2me | Theorems.Thm_BianchiIX_gaussCode_recurrence
-- name    : BianchiIX.gaussCode_recurrence
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T14:42:08.694594+00:00
-- url     : https://prove2.me/theorems/2fa97c0b-1952-4e29-9046-5c39b6390718
-- title:
--   Inverse recurrence for the continued-fraction code
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
--   For every positive digit sequence $a$,
--   $$\pi(a)=\frac1{a_0+\pi(\sigma a)}.$$
--   This identity relates the code of a sequence to that of its tail.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/GaussCoding.lean#L112-L118

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

theorem BianchiIX.gaussCode_recurrence (a : ℕ → ℕ+) :
    gaussCode a = gaussInv (a 0) (gaussCode (shiftDigits a 1)) := by sorry
