-- Prove2me | Theorems.Thm_Corless_Dv_sub_mod4
-- name    : Corless.Dv_sub_mod4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:41:07.275182+00:00
-- url     : https://prove2.me/theorems/40955b3b-3645-469e-8db5-94456911c3cd
-- title:
--   Corless: Dv sub mod4
-- statement:
--   Modulo 4, the difference only sees which signs differ: with `s j - t j = 2 δ j`,
--   `D s - D t ≡ 2 ∑ δ j · X · f j · f (M - 2 - j)`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CorlessNilpotent/Main.lean#L63-L84
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CorlessNilpotent/Main.lean#L63-L84

module
public import Mathlib.Algebra.BigOperators.Intervals
public import Definitions.Def_LeanPool_CorlessNilpotent_Parity
public import Definitions.Def_LeanPool_CorlessNilpotent_Main
set_option autoImplicit true
@[expose] public section
public section
open Polynomial Finset
open Corless

theorem Corless.Dv_sub_mod4 {s t : ℕ → ℤ} {M : ℕ} (hs : IsSign s M) (ht : IsSign t M) (δ : ℕ → ℤ)
    (hδ : ∀ j, j + 1 < M → s j - t j = 2 * δ j) :
    ∃ R : ℤ[X], Dv s M - Dv t M
      = 2 * ∑ j ∈ range (M - 1), C (δ j) * X * f j * f (M - 2 - j) + 4 * R := by sorry
