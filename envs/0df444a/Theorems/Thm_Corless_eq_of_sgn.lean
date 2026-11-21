-- Prove2me | Theorems.Thm_Corless_eq_of_sgn
-- name    : Corless.eq_of_sgn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:42:20.212325+00:00
-- url     : https://prove2.me/theorems/7b3d22ec-dd33-4e46-bb09-a5e7a996b029
-- title:
--   Corless: eq of sgn
-- statement:
--   An entry in `{1, i}` is determined by its sign.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CorlessNilpotent/Vectors.lean#L154-L160
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CorlessNilpotent/Vectors.lean#L154-L160

module
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Set.Card
public import Definitions.Def_LeanPool_CorlessNilpotent_Matrix
public import Definitions.Def_LeanPool_CorlessNilpotent_Vectors
set_option autoImplicit true
@[expose] public section
public section
open Polynomial
open Corless

theorem Corless.eq_of_sgn {x y : ℂ} (hx : x = 1 ∨ x = Complex.I) (hy : y = 1 ∨ y = Complex.I)
    (h : entrySign x = entrySign y) : x = y := by sorry
