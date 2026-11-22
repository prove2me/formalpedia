-- Prove2me | Theorems.Thm_CircuitComplexity_CNF_eval_neg
-- name    : CircuitComplexity.CNF.eval_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:09:36.05296+00:00
-- url     : https://prove2.me/theorems/bb417230-3e09-40c1-98a8-65066b5bee08
-- title:
--   CNF: eval neg
-- statement:
--   Negating a CNF formula negates its evaluation (De Morgan duality).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/NF/Defs.lean#L116-L119
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/NF/Defs.lean#L116-L119

module
public import Definitions.Def_LeanPool_CircuitComplexity_Basic
public import Definitions.Def_LeanPool_CircuitComplexity_NF_Defs
set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity

theorem CircuitComplexity.CNF.eval_neg (φ : CNF N) (x : BitString N) :
    φ.neg.eval x = !(φ.eval x) := by sorry
