-- Prove2me | Theorems.Thm_Corless_folded_sizes
-- name    : Corless.folded_sizes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:40:25.70144+00:00
-- url     : https://prove2.me/theorems/35c564d5-67f2-4a78-84c6-8bd4b59564e3
-- title:
--   Corless: folded sizes
-- statement:
--   The half and full path sizes expressed using the length of the half's edge sequence.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CorlessNilpotent/Parity.lean#L80-L87
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CorlessNilpotent/Parity.lean#L80-L87

module
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.CharP.Reduced
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Tactic.LinearCombination
public import Definitions.Def_LeanPool_CorlessNilpotent_Path
public import Definitions.Def_LeanPool_CorlessNilpotent_Parity
set_option autoImplicit true
@[expose] public section
public section
open Polynomial Finset
open Corless

theorem Corless.folded_sizes (k : ℕ) :
    2 ^ (k + 1) - 1 = 2 ^ (k + 1) - 2 + 1 ∧
      2 ^ (k + 2) - 1 = 2 * (2 ^ (k + 1) - 2) + 3 := by sorry
