-- Prove2me | Theorems.Thm_Corless_folded_edges
-- name    : Corless.folded_edges
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:40:29.415715+00:00
-- url     : https://prove2.me/theorems/8e7ef037-a46b-4056-8116-0cebcdf5a6ce
-- title:
--   Corless: folded edges
-- statement:
--   Folding duplicates the half-path edges and adds two middle edges.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CorlessNilpotent/Parity.lean#L90-L92
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CorlessNilpotent/Parity.lean#L90-L92

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

theorem Corless.folded_edges (k : ℕ) : 2 ^ (k + 2) - 2 = 2 * (2 ^ (k + 1) - 2) + 2 := by sorry
