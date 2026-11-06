-- Prove2me | Theorems.Thm_BianchiIX_norm_le_exp_of_norm_deriv_budget
-- name    : BianchiIX.norm_le_exp_of_norm_deriv_budget
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T06:54:45.053672+00:00
-- url     : https://prove2.me/theorems/792d945d-53d7-42d0-8b76-fb2002c60cf7
-- title:
--   A nondecreasing forcing budget bounds variable-rate norm growth
-- statement:
--   Let $E$ be a real normed space. On $[a,b]$, let
--   $f:\mathbb R\to E$ and real functions $z,B$ have derivatives.
--   Assume $B(t),B'(t)\geq0$, $\|f(a)\|\leq B(a)$, $z(t)\geq z(a)$,
--   and $\|f'(t)\|\leq z'(t)\|f(t)\|+B'(t)$. Then
--   $$\|f(t)\|\leq B(t)\exp(z(t)-z(a))\quad(t\in[a,b]).$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/NormIntegralForcing.lean#L13-L52

import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.ProjIcc

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX
open Set MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem BianchiIX.norm_le_exp_of_norm_deriv_budget {f f' : ℝ → E} {z z' B B' : ℝ → ℝ} {a b : ℝ}
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (hz : ∀ t ∈ Icc a b, HasDerivAt z (z' t) t)
    (hB : ∀ t ∈ Icc a b, HasDerivAt B (B' t) t)
    (hB0 : ∀ t ∈ Icc a b, 0 ≤ B t) (hB' : ∀ t ∈ Icc a b, 0 ≤ B' t)
    (hinit : ‖f a‖ ≤ B a) (hclock : ∀ t ∈ Icc a b, z a ≤ z t)
    (hbound : ∀ t ∈ Icc a b, ‖f' t‖ ≤ z' t * ‖f t‖ + B' t) :
    ∀ t ∈ Icc a b, ‖f t‖ ≤ B t * Real.exp (z t - z a) := by sorry
