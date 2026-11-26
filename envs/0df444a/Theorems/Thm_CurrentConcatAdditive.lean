-- Prove2me | Theorems.Thm_CurrentConcatAdditive
-- name    : CurrentConcatAdditive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:49:40.150424+00:00
-- url     : https://prove2.me/theorems/c288d12b-f400-54e8-bbb6-0beb19bcf415
-- title:
--   Current Concat Additive: Current Concat Additive
-- statement:
--   The current of a concatenation is the sum of the currents of the pieces.
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/CurrentConcatAdditive.lean#L9-L91
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/CurrentConcatAdditive.lean#L9-L91

import Definitions.Def_Tablet_curveCurrent
import Definitions.Def_Tablet_curveConcat
import Definitions.Def_Tablet_CurveLipschitz
import Definitions.Def_Tablet_CurrentConcatAdditive
import Theorems.Thm_CurveLipschitz

set_option autoImplicit false
open Set MeasureTheory

theorem CurrentConcatAdditive {E : Type*} [MetricSpace E] (γ₁ γ₂ : Curve E)
    (h : γ₁.toFun γ₁.len = γ₂.toFun 0) (ω : Form1 E) :
    curveCurrent (curveConcat γ₁ γ₂ h) ω = curveCurrent γ₁ ω + curveCurrent γ₂ ω := by sorry
