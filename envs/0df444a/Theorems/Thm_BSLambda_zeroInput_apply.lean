-- Prove2me | Theorems.Thm_BSLambda_zeroInput_apply
-- name    : BSLambda.zeroInput_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:46:27.162701+00:00
-- url     : https://prove2.me/theorems/f1207388-f8cb-4997-b196-6d9017dc8439
-- title:
--   BSLambda: zero Input apply
-- statement:
--   The BSLambda construction uses the zero Input apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Cube.lean#L40-L40
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Cube.lean#L40-L40

module
public import Mathlib.InformationTheory.Hamming
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
set_option autoImplicit true
@[expose] public section
public section
open BSLambda

theorem BSLambda.zeroInput_apply {V : Type*} (v : V) : zeroInput V v = false := by sorry

attribute [defeq] BSLambda.zeroInput_apply
