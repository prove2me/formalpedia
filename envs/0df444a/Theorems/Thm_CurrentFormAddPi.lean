-- Prove2me | Theorems.Thm_CurrentFormAddPi
-- name    : CurrentFormAddPi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:53:01.617307+00:00
-- url     : https://prove2.me/theorems/8cff4fe4-a363-559c-b503-50ac47b0cae1
-- title:
--   Current Form Add Pi: Current Form Add Pi
-- statement:
--   `curveCurrent γ ·` is additive in the `π` slot of a `1`-form, holding `f` fixed
--   (paper.tex 1400, "use multilinearity"). Unlike the `f`-slot case (`\noderef{CurrentFormAddF}`),
--   this needs a genuine argument: `deriv` is additive only where both summands are differentiable,
--   which for the Lipschitz (hence absolutely continuous) maps `ω1.pi ∘ γ` and `ω2.pi ∘ γ` holds
--   almost everywhere on the interval of integration.
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/CurrentFormAddPi.lean#L12-L47
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/CurrentFormAddPi.lean#L12-L47

import Definitions.Def_Tablet_curveCurrent
import Definitions.Def_Tablet_CurveLipschitz
import Definitions.Def_Tablet_CurrentFormAddPi
import Theorems.Thm_CurveLipschitz

set_option autoImplicit false
open MeasureTheory

theorem CurrentFormAddPi {E : Type*} [MetricSpace E] (γ : Curve E) (ω1 ω2 ω12 : Form1 E)
    (hf1 : ω1.f = ω12.f) (hf2 : ω2.f = ω12.f)
    (hpi : ∀ x, ω12.pi x = ω1.pi x + ω2.pi x) :
    curveCurrent γ ω12 = curveCurrent γ ω1 + curveCurrent γ ω2 := by sorry
