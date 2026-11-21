-- Prove2me | Theorems.Thm_Corless_corless_conjecture
-- name    : Corless.corless_conjecture
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:42:26.255652+00:00
-- url     : https://prove2.me/theorems/d77c4ea7-fbfe-4697-a747-02c0038375f1
-- title:
--   Corless: corless conjecture
-- statement:
--   **Corless's Conjecture 5.1.** For a vector `u` with entries in `{1, i}`, the
--   skew-symmetric tridiagonal matrix `T_{|u|+1}(u)` is nilpotent iff `u` is one of Corless's
--   recursively constructed vectors.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CorlessNilpotent/Vectors.lean#L226-L234
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CorlessNilpotent/Vectors.lean#L226-L234

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

theorem Corless.corless_conjecture {u : List ℂ} (hu : ∀ x ∈ u, x = 1 ∨ x = Complex.I) :
    IsNilpotent (T (u.length + 1) (fun i => u.getD i 1)) ↔ ∃ k, CorlessVec k u := by sorry
