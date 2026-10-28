-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_RelativeObservationBounds_relative_quotient_bounds
-- name    : CountingMatroid.Analysis.RelativeObservationBounds.relative_quotient_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T14:04:57.199028+00:00
-- url     : https://prove2.me/theorems/137109c7-fa6d-4b84-bc8d-172ea6086f27
-- title:
--   Relative errors give two-sided quotient bounds
-- statement:
--   Let $\eta,a,b,x,y\in\mathbb Q$ with $0\le\eta<1$, $a>0$, and $b>0$. Suppose $x$ and $y$ estimate $a$ and $b$ within multiplicative error $\eta$: $$(1-\eta)a\le x\le(1+\eta)a,\qquad(1-\eta)b\le y\le(1+\eta)b.$$ Then $x,y>0$ and $$\frac{1-\eta}{1+\eta}\le\frac{x/y}{a/b}\le\frac{1+\eta}{1-\eta}.$$
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/RelativeObservationBounds.lean#L13-L39

import Definitions.Def_CountingMatroid_Analysis_RelativeObservationBounds
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace CountingMatroid.Analysis.RelativeObservationBounds
end CountingMatroid.Analysis.RelativeObservationBounds
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.RelativeObservationBounds

theorem CountingMatroid.Analysis.RelativeObservationBounds.relative_quotient_bounds (η a b x y : ℚ)
    (hη : 0 ≤ η) (hηlt : η < 1) (ha : 0 < a) (hb : 0 < b)
    (hx : RelativeEstimate η a x) (hy : RelativeEstimate η b y) :
    0 < x ∧ 0 < y ∧
      (1 - η) / (1 + η) ≤ (x / y) / (a / b) ∧
      (x / y) / (a / b) ≤ (1 + η) / (1 - η) := by sorry
