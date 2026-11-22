-- Prove2me | Theorems.Thm_CircuitComplexity_DNF_eval_neg
-- name    : CircuitComplexity.DNF.eval_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:09:34.805461+00:00
-- url     : https://prove2.me/theorems/101b4cba-6739-4eb5-99d4-ffbf77f6ea15
-- title:
--   DNF: eval neg
-- statement:
--   Negating a DNF formula negates its evaluation (De Morgan duality).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/NF/Defs.lean#L122-L125
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/NF/Defs.lean#L122-L125

module
public import Definitions.Def_LeanPool_CircuitComplexity_Basic
public import Definitions.Def_LeanPool_CircuitComplexity_NF_Defs
set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity

theorem CircuitComplexity.DNF.eval_neg (φ : DNF N) (x : BitString N) :
    φ.neg.eval x = !(φ.eval x) := by sorry
