-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_RelativeObservationBounds_learned_multiplier_bounds
-- name    : CountingMatroid.Analysis.RelativeObservationBounds.learned_multiplier_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T14:06:15.734866+00:00
-- url     : https://prove2.me/theorems/0aa11375-0f51-4f92-ab19-14c3e1de514a
-- title:
--   Relative type estimates and ideal drift yield factor-four multipliers
-- statement:
--   Let $\eta,w,p_0,p_i,x,y,I,J\in\mathbb Q$, with $0\le\eta\le1/3$ and $w,p_0,p_i>0$. Assume $$(1-\eta)p_0\le x\le(1+\eta)p_0,\qquad(1-\eta)p_i\le y\le(1+\eta)p_i,$$ and suppose $$I=\frac{wp_0}{p_i},\qquad I/2\le J\le2I.$$ Then the updated multiplier satisfies $$J/4\le\frac{wx}{y}\le4J.$$
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/RelativeObservationBounds.lean#L41-L68

import Definitions.Def_CountingMatroid_Analysis_RelativeObservationBounds
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace CountingMatroid.Analysis.RelativeObservationBounds
end CountingMatroid.Analysis.RelativeObservationBounds
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.RelativeObservationBounds

theorem CountingMatroid.Analysis.RelativeObservationBounds.learned_multiplier_bounds (η w p₀ pᵢ x y ideal nextIdeal : ℚ)
    (hη : 0 ≤ η) (hηsmall : η ≤ 1 / 3)
    (hw : 0 < w) (hp₀ : 0 < p₀) (hpᵢ : 0 < pᵢ)
    (hx : RelativeEstimate η p₀ x) (hy : RelativeEstimate η pᵢ y)
    (hideal : w * p₀ / pᵢ = ideal)
    (hdrift : ideal / 2 ≤ nextIdeal ∧ nextIdeal ≤ 2 * ideal) :
    nextIdeal / 4 ≤ w * x / y ∧ w * x / y ≤ 4 * nextIdeal := by sorry
