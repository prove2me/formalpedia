-- Prove2me | Theorems.Thm_Corless_dimension
-- name    : Corless.dimension
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:40:38.249095+00:00
-- url     : https://prove2.me/theorems/f60f82ff-aec4-4e1e-beee-42f453894bef
-- title:
--   Corless: dimension
-- statement:
--   Corless's dimension theorem: if `D = 1` for a sign sequence on a path with `m ≥ 1` vertices,
--   then `m = 2^(k+1) - 1` for some `k`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CorlessNilpotent/Parity.lean#L183-L200
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CorlessNilpotent/Parity.lean#L183-L200

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

theorem Corless.dimension {s : ℕ → ℤ} {m : ℕ} (hs : IsSign s m) (hm : 1 ≤ m) (h : Dv s m = 1) :
    ∃ k, m = 2 ^ (k + 1) - 1 := by sorry
