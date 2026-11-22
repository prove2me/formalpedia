-- Prove2me | Theorems.Thm_CircuitComplexity_andOr2_fanIn
-- name    : CircuitComplexity.andOr2_fanIn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:09:24.515872+00:00
-- url     : https://prove2.me/theorems/2a75bd7d-61f1-4f45-b4b7-98481ad68dbe
-- title:
--   Circuit Complexity: and Or2 fan In
-- statement:
--   Every gate over `Basis.andOr2` has fan-in exactly 2.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/AON/Defs.lean#L67-L67
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/AON/Defs.lean#L67-L67

module
public import Definitions.Def_LeanPool_CircuitComplexity_Basic
public import Definitions.Def_LeanPool_CircuitComplexity_AON_Defs
set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity

theorem CircuitComplexity.andOr2_fanIn {W : Nat} (g : Gate Basis.andOr2 W) : g.fanIn = 2 := by sorry
