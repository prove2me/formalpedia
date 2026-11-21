-- Prove2me | Theorems.Thm_Corless_corless
-- name    : Corless.corless
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:41:38.313244+00:00
-- url     : https://prove2.me/theorems/1aebbd57-a1bf-4f31-876e-2bd9f1d93da2
-- title:
--   Corless: corless
-- statement:
--   **Corless's conjecture.** For a sign sequence `s`, the weighted path with `m ≥ 1` vertices has
--   `D = 1` (equivalently: the skew-symmetric tridiagonal matrix with superdiagonal `u`, `u² = s`, is
--   nilpotent) exactly when `m = 2^(k+1) - 1` and the signs form one of Corless's sequences.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CorlessNilpotent/Main.lean#L284-L291
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CorlessNilpotent/Main.lean#L284-L291

module
public import Mathlib.Algebra.BigOperators.Intervals
public import Definitions.Def_LeanPool_CorlessNilpotent_Parity
public import Definitions.Def_LeanPool_CorlessNilpotent_Main
set_option autoImplicit true
@[expose] public section
public section
open Polynomial Finset
open Corless

theorem Corless.corless {s : ℕ → ℤ} {m : ℕ} (hs : IsSign s m) (hm : 1 ≤ m) :
    Dv s m = 1 ↔ ∃ k, m = 2 ^ (k + 1) - 1 ∧ Fam k s := by sorry
