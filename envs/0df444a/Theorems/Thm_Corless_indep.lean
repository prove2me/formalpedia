-- Prove2me | Theorems.Thm_Corless_indep
-- name    : Corless.indep
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:41:00.252673+00:00
-- url     : https://prove2.me/theorems/78e86ab8-c3e5-42d7-8a39-0648f76b2175
-- title:
--   Corless: indep
-- statement:
--   Lemma 3 (independence): the polynomials `fbar j * fbar (2N - 1 - j)`, `j < N`, are linearly
--   independent over 𝔽₂.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CorlessNilpotent/Main.lean#L118-L155
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CorlessNilpotent/Main.lean#L118-L155

module
public import Mathlib.Algebra.BigOperators.Intervals
public import Definitions.Def_LeanPool_CorlessNilpotent_Parity
public import Definitions.Def_LeanPool_CorlessNilpotent_Main
set_option autoImplicit true
@[expose] public section
public section
open Polynomial Finset
open Corless

theorem Corless.indep (N : ℕ) (w : ℕ → ZMod 2)
    (h : ∑ j ∈ range N, C (w j) * (fbar j * fbar (2 * N - 1 - j)) = 0) : ∀ j < N, w j = 0 := by sorry
