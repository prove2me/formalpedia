-- Prove2me | Theorems.Thm_CircuitComplexity_CNF_neg_complexity
-- name    : CircuitComplexity.CNF.neg_complexity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:09:35.806579+00:00
-- url     : https://prove2.me/theorems/b268a18c-7950-42ed-8673-78bd3ef4c193
-- title:
--   CNF: neg complexity
-- statement:
--   Negating a CNF preserves complexity.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/NF/Defs.lean#L128-L129
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/NF/Defs.lean#L128-L129

module
public import Definitions.Def_LeanPool_CircuitComplexity_Basic
public import Definitions.Def_LeanPool_CircuitComplexity_NF_Defs
set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity

theorem CircuitComplexity.CNF.neg_complexity (φ : CNF N) : φ.neg.complexity = φ.complexity := by sorry
