-- Prove2me | Theorems.Thm_BianchiIX_gaussMap_iterate_code
-- name    : BianchiIX.gaussMap_iterate_code
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T14:45:20.529233+00:00
-- url     : https://prove2.me/theorems/4e747ec9-b3df-46eb-b5de-3e1fdfb49a16
-- title:
--   Gauss iteration corresponds to shifting the digit sequence
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
--   For every $a\in A^{\mathbb N}$ and $n\in\mathbb N$,
--   $$T^n(\pi(a))=\pi(\sigma^n a).$$
--   The coding therefore intertwines the shift with the Gauss map.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/GaussCoding.lean#L169-L174

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

theorem BianchiIX.gaussMap_iterate_code (a : ℕ → ℕ+) (n : ℕ) :
    gaussMap^[n] (gaussCode a) = gaussCode (shiftDigits a n) := by sorry
