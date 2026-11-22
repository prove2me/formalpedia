-- Prove2me | Theorems.Thm_CircuitComplexity_Literal_eval_neg
-- name    : CircuitComplexity.Literal.eval_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:09:35.517513+00:00
-- url     : https://prove2.me/theorems/86f69604-b986-4164-8cc1-cc9b6f60babb
-- title:
--   Literal: eval neg
-- statement:
--   Negating a literal negates its evaluation.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/NF/Defs.lean#L51-L55
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/NF/Defs.lean#L51-L55

module
public import Definitions.Def_LeanPool_CircuitComplexity_Basic
public import Definitions.Def_LeanPool_CircuitComplexity_NF_Defs
set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity

theorem CircuitComplexity.Literal.eval_neg (l : Literal N) (x : BitString N) :
    l.neg.eval x = !(l.eval x) := by sorry
