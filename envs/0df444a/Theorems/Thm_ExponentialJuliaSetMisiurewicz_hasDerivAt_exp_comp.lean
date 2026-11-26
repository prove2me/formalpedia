-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_hasDerivAt_exp_comp
-- name    : ExponentialJuliaSetMisiurewicz.hasDerivAt_exp_comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:58:12.728275+00:00
-- url     : https://prove2.me/theorems/85d17abf-291a-46b2-873f-86368c3fed0b
-- title:
--   Exponential Julia Set Misiurewicz: has Deriv At exp comp
-- statement:
--   Chain rule for the exponential, corresponding to
--   `HAS_COMPLEX_DERIVATIVE_CEXP_COMPOSE` in HOL Light.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Basic.lean#L81-L86
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Basic.lean#L81-L86

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Continuity
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Definitions.Def_ExpChaotic_Basic
set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section

theorem ExponentialJuliaSetMisiurewicz.hasDerivAt_exp_comp {f : ℂ → ℂ} {f' z : ℂ}
    (hf : HasDerivAt f f' z) :
    HasDerivAt (Complex.exp ∘ f)
      (f' * Complex.exp (f z)) z := by sorry
