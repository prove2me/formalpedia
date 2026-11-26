-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_expIterate_succ
-- name    : ExponentialJuliaSetMisiurewicz.expIterate_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:58:10.655403+00:00
-- url     : https://prove2.me/theorems/e5f75085-29f7-4cee-8283-65c48e173d33
-- title:
--   Exponential Julia Set Misiurewicz: exp Iterate succ
-- statement:
--   Apply one more exponential after the `n`-th iterate.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Basic.lean#L56-L59
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Basic.lean#L56-L59

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

theorem ExponentialJuliaSetMisiurewicz.expIterate_succ (n : ℕ) (z : ℂ) :
    expIterate (n + 1) z =
      Complex.exp (expIterate n z) := by sorry
