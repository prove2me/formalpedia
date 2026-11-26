-- Prove2me | Theorems.Thm_CurveConcatEndpoints
-- name    : CurveConcatEndpoints
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:56:04.318269+00:00
-- url     : https://prove2.me/theorems/3cfc17d6-8591-550a-bafa-5074c0db3a59
-- title:
--   Curve Concat Endpoints: Curve Concat Endpoints
-- statement:
--   The concatenation `γ₁ * γ₂` starts where `γ₁` starts and ends where `γ₂` ends (currently
--   re-derived inline both inside `curveSampling`'s own definition and inside `SamplingEndpoints`;
--   `ClosingUp` needs it a third time, to show that a sampled-and-closed-off curve is closed).
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/CurveConcatEndpoints.lean#L9-L24
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/CurveConcatEndpoints.lean#L9-L24

import Definitions.Def_Tablet_curveConcat
import Definitions.Def_Tablet_CurveConcatEndpoints
set_option autoImplicit false
open Set

theorem CurveConcatEndpoints {E : Type*} [MetricSpace E] (γ₁ γ₂ : Curve E)
    (h : γ₁.toFun γ₁.len = γ₂.toFun 0) :
    (curveConcat γ₁ γ₂ h).toFun 0 = γ₁.toFun 0 ∧
      (curveConcat γ₁ γ₂ h).toFun (curveConcat γ₁ γ₂ h).len = γ₂.toFun γ₂.len := by sorry
