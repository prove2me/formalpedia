-- Prove2me | Theorems.Thm_CircuitComplexity_CompileAON_oOffset_succ
-- name    : CircuitComplexity.CompileAON.oOffset_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:12:46.542804+00:00
-- url     : https://prove2.me/theorems/df18d52b-baf0-45fd-83a4-819ab0820d1d
-- title:
--   Compile AON: o Offset succ
-- statement:
--   The Compile AON construction uses the o Offset succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/Simulation.lean#L208-L210
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/Simulation.lean#L208-L210

module
public import Definitions.Def_LeanPool_CircuitComplexity_AON_Defs
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_AON
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_Simulation
set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity
open CircuitComplexity.CompileAON
variable {N M G : Nat} [NeZero N] [NeZero M]

theorem CircuitComplexity.CompileAON.oOffset_succ (c : Circuit Basis.unboundedAON N M G) {j : Nat} (hj : j < M) :
    oOffset c (j + 1) = oOffset c j + chainLen (c.outputs ⟨j, hj⟩).fanIn := by sorry
