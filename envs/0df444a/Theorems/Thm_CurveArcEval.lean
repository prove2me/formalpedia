-- Prove2me | Theorems.Thm_CurveArcEval
-- name    : CurveArcEval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:02:36.590553+00:00
-- url     : https://prove2.me/theorems/ebb470dc-6d80-5582-acbb-96faf146a1ec
-- title:
--   Curve Arc Eval: Curve Arc Eval
-- statement:
--   The arc-to-ambient evaluation dictionary for the counter-clockwise circular arc
--   `A := γ|_{[t,t']}` (`curveArc`) of a closed curve `γ`, uniform in the order of `t,t'`. Writing
--   `ℓ(a,b) := b - a` when `a ≤ b` and `ℓ(a,b) := (γ.len - a) + b` otherwise for the ccw arc length
--   from `a` to `b`, it says: the arc's length is `ℓ(t,t')`, and there is a reparametrization
--   `σ : ℝ → ℝ` of the arc's own parameter interval `[0,A.len]` back into `γ`'s parameter interval
--   `[0,γ.len]` which starts at `t`, satisfies `A p = γ (σ p)` throughout, ends at `t'` *as a point of
--   `E`* (`γ (σ A.len) = γ t'`; in the wrap case with `t' = 0` one has `σ A.len = γ.len ≠ t'`, and only
--   closedness of `γ` rescues the identity), and is an isometry for ccw arc length:
--   `ℓ(σ p, σ p') = p' - p` whenever `p ≤ p'` in `[0,A.len]`.
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/CurveArcEval.lean#L15-L119
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/CurveArcEval.lean#L15-L119

import Definitions.Def_Tablet_curveArc
import Definitions.Def_Tablet_CurveArcEval
set_option autoImplicit false
open Set

theorem CurveArcEval {E : Type*} [MetricSpace E] (γ : Curve E) (hcl : IsClosedCurve γ)
    (t t' : ℝ) (ht0 : 0 ≤ t) (htl : t ≤ γ.len) (ht'0 : 0 ≤ t') (ht'l : t' ≤ γ.len) :
    (curveArc γ hcl t t' ht0 htl ht'0 ht'l).len
        = (if t ≤ t' then t' - t else (γ.len - t) + t') ∧
      ∃ σ : ℝ → ℝ,
        σ 0 = t ∧
        γ.toFun (σ (curveArc γ hcl t t' ht0 htl ht'0 ht'l).len) = γ.toFun t' ∧
        (∀ p ∈ Set.Icc (0 : ℝ) (curveArc γ hcl t t' ht0 htl ht'0 ht'l).len,
          σ p ∈ Set.Icc (0 : ℝ) γ.len ∧
            (curveArc γ hcl t t' ht0 htl ht'0 ht'l).toFun p = γ.toFun (σ p)) ∧
        (∀ p ∈ Set.Icc (0 : ℝ) (curveArc γ hcl t t' ht0 htl ht'0 ht'l).len,
          ∀ p' ∈ Set.Icc (0 : ℝ) (curveArc γ hcl t t' ht0 htl ht'0 ht'l).len, p ≤ p' →
            (if σ p ≤ σ p' then σ p' - σ p else (γ.len - σ p) + σ p') = p' - p) := by sorry
