-- Prove2me | Theorems.Thm_Corless_card_nilpotent
-- name    : Corless.card_nilpotent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:43:11.66929+00:00
-- url     : https://prove2.me/theorems/08e4b91b-432c-461e-b76b-237269868c13
-- title:
--   Corless: card nilpotent
-- statement:
--   **The count.** Exactly `2^k` vectors `u` of length `2^(k+1) - 2` with entries in `{1, i}` give
--   a nilpotent `T(u)`. Since `u` is the superdiagonal of `T(u)`, these are `2^k` distinct matrices of
--   dimension `2^(k+1) - 1` (Corless's `2^(K-1)` in dimension `2^K - 1`). In every other dimension
--   there are none, by `T_nilpotent_iff`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CorlessNilpotent/Vectors.lean#L290-L310
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CorlessNilpotent/Vectors.lean#L290-L310

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

theorem Corless.card_nilpotent (k : ℕ) :
    {u : List ℂ | u.length = 2 ^ (k + 1) - 2 ∧ (∀ x ∈ u, x = 1 ∨ x = Complex.I) ∧
      IsNilpotent (T (u.length + 1) (fun i => u.getD i 1))}.ncard = 2 ^ k := by sorry
