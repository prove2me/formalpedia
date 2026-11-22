-- Prove2me | Theorems.Thm_CircuitComplexity_CNF_size_toCircuit
-- name    : CircuitComplexity.CNF.size_toCircuit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:11:46.958302+00:00
-- url     : https://prove2.me/theorems/b147e5e8-2d34-4eb5-a93d-a84fb6b9660a
-- title:
--   CNF: size to Circuit
-- statement:
--   The circuit size of `toCircuit` is `φ.complexity + 1`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/NF.lean#L156-L157
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/NF.lean#L156-L157

module
public import Definitions.Def_LeanPool_CircuitComplexity_NF_Defs
public import Definitions.Def_LeanPool_CircuitComplexity_AON_Defs
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.BigOperators
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_NF
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit true
set_option autoImplicit true
open CircuitComplexity
open CircuitComplexity.CNF

theorem CircuitComplexity.CNF.size_toCircuit [NeZero N] (φ : CNF N) :
    φ.toCircuit.size = φ.complexity + 1 := by sorry
