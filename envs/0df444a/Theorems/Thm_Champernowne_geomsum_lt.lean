-- Prove2me | Theorems.Thm_Champernowne_geomsum_lt
-- name    : Champernowne.geomsum_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:37:44.431474+00:00
-- url     : https://prove2.me/theorems/530abd53-0a72-4962-811a-4991e8e31a17
-- title:
--   Champernowne: geomsum lt
-- statement:
--   `∑_{i<K} b^i < b^K` for `1 < b`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/DigitCount.lean#L114-L121
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/DigitCount.lean#L114-L121

module
public import Definitions.Def_LeanPool_Champernowne_Count
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_Champernowne_DigitCount
set_option autoImplicit true
@[expose] public section
public section
open Champernowne

theorem Champernowne.geomsum_lt {b : ℕ} (hb : 1 < b) (K : ℕ) :
    ∑ i ∈ Finset.range K, b ^ i < b ^ K := by sorry
