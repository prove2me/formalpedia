-- Prove2me | Theorems.Thm_ClassicalComplexWPT_exists_lastSlice_eq_pow_mul
-- name    : ClassicalComplexWPT.exists_lastSlice_eq_pow_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:56:20.708097+00:00
-- url     : https://prove2.me/theorems/162b784d-c47a-5a83-a908-b27da347f948
-- title:
--   Classical Complex WPT: exists last Slice eq pow mul
-- statement:
--   The exact-order hypothesis supplies the normalized one-variable axis factorization.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/ExactOrder.lean#L51-L61
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/ExactOrder.lean#L51-L61

import Definitions.Def_ClassicalComplexWPT_Basic
import Mathlib.Analysis.Analytic.Order
import Definitions.Def_ClassicalComplexWPT_ExactOrder
set_option autoImplicit true
open scoped Topology
open ClassicalComplexWPT

theorem ClassicalComplexWPT.exists_lastSlice_eq_pow_mul {n d : ℕ} {f : Ambient n → ℂ}
    (hf : AnalyticAt ℂ f 0) (horder : ExactOrderInLastVariable f d) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧ g 0 ≠ 0 ∧
      lastSlice f =ᶠ[𝓝 0] fun w ↦ w ^ d * g w := by sorry
