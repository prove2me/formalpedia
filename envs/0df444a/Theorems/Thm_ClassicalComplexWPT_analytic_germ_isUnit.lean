-- Prove2me | Theorems.Thm_ClassicalComplexWPT_analytic_germ_isUnit
-- name    : ClassicalComplexWPT.analytic_germ_isUnit
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T17:57:20.32529+00:00
-- url     : https://prove2.me/theorems/40e9757a-bd12-459d-b895-7011a17f449b
-- title:
--   Classical Complex WPT: analytic germ is Unit
-- statement:
--   A nonvanishing analytic germ is a ring-theoretic unit.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/Germs.lean#L29-L33
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/Germs.lean#L29-L33

import Definitions.Def_ClassicalComplexWPT_Basic
import Mathlib.Order.Filter.Germ.Basic
import Definitions.Def_ClassicalComplexWPT_Germs
set_option autoImplicit true
open Filter
open scoped Topology
open ClassicalComplexWPT

theorem ClassicalComplexWPT.analytic_germ_isUnit {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {g : E → ℂ} {x : E} (hg : AnalyticAt ℂ g x) (hg0 : g x ≠ 0) :
    IsUnit (g : Filter.Germ (𝓝 x) ℂ) := by sorry
