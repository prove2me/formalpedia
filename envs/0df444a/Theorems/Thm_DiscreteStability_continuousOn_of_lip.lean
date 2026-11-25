-- Prove2me | Theorems.Thm_DiscreteStability_continuousOn_of_lip
-- name    : DiscreteStability.continuousOn_of_lip
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T08:32:28.093361+00:00
-- url     : https://prove2.me/theorems/e1dfa8fe-f6cb-5d68-bc72-261539c89b9c
-- title:
--   Discrete Stability: continuous On of lip
-- statement:
--   A map that is `L`-Lipschitz on `S` (in the form `‖g u - g v‖ ≤ L ‖u - v‖`) is continuous on `S`.
--
--   Source: https://github.com/magbenji/discrete-modified-gradient-lean/blob/c3e4688e6f32de6904ce696890a372ae4cba6ad3/DiscreteStability/Basic.lean#L99-L109
-- source:
--   https://github.com/magbenji/discrete-modified-gradient-lean/blob/c3e4688e6f32de6904ce696890a372ae4cba6ad3/DiscreteStability/Basic.lean#L99-L109

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Definitions.Def_DiscreteStability_Basic
set_option autoImplicit true
open scoped RealInnerProductSpace
open DiscreteStability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
omit [InnerProductSpace ℝ E]

theorem DiscreteStability.continuousOn_of_lip {F : Type*} [NormedAddCommGroup F] {g : E → F} {S : Set E} {L : ℝ}
    (hL : 0 ≤ L) (h : ∀ u ∈ S, ∀ v ∈ S, ‖g u - g v‖ ≤ L * ‖u - v‖) : ContinuousOn g S := by sorry
