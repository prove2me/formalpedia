-- Prove2me | Theorems.Thm_CircuitComplexity_DNF_size_toCircuit
-- name    : CircuitComplexity.DNF.size_toCircuit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:11:54.492966+00:00
-- url     : https://prove2.me/theorems/1b2c90f8-2ba1-4ddf-b768-308301318e3f
-- title:
--   DNF: size to Circuit
-- statement:
--   The circuit size of `toCircuit` is `φ.complexity + 1`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/NF.lean#L222-L223
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/NF.lean#L222-L223

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
open CircuitComplexity.DNF

theorem CircuitComplexity.DNF.size_toCircuit [NeZero N] (φ : DNF N) :
    φ.toCircuit.size = φ.complexity + 1 := by sorry
