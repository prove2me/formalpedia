-- Prove2me | Theorems.Thm_BianchiIX_gaussCode_shadowing
-- name    : BianchiIX.gaussCode_shadowing
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T14:52:32.168674+00:00
-- url     : https://prove2.me/theorems/add08d0e-3056-4f36-96ea-6e1882fe19ba
-- title:
--   Vanishing errors give agreement with a coded Gauss orbit
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
--   Suppose $y_m\in[0,1]$ for every $m$ and $e_m\to0$. Then
--   $$y_m-T^m(\pi(a))\longrightarrow0.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/GaussCoding.lean#L261-L268

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

theorem BianchiIX.gaussCode_shadowing (a : ℕ → ℕ+) {y : ℕ → ℝ}
    (hy : ∀ m, y m ∈ Icc (0 : ℝ) 1)
    (herror : Tendsto (inverseError (fun k => (a k : ℕ)) y) atTop (𝓝 0)) :
    Tendsto (fun m => y m - gaussMap^[m] (gaussCode a)) atTop (𝓝 0) := by sorry
