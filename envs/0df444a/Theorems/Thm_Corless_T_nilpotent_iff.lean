-- Prove2me | Theorems.Thm_Corless_T_nilpotent_iff
-- name    : Corless.T_nilpotent_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:42:10.784797+00:00
-- url     : https://prove2.me/theorems/4457fdf1-018f-43f1-9dc8-bd41a9e6ba15
-- title:
--   Corless: T nilpotent iff
-- statement:
--   **Corless's conjecture, matrix form.** For `u` with entries in `{1, i}`, the matrix `T m u`
--   is nilpotent iff the signs `u²` satisfy `Dv = 1`, i.e. (by `corless`) iff `m = 2^(k+1) - 1` and
--   the signs form one of Corless's sequences.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CorlessNilpotent/Matrix.lean#L214-L226
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CorlessNilpotent/Matrix.lean#L214-L226

module
public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.Data.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Definitions.Def_LeanPool_CorlessNilpotent_Main
public import Definitions.Def_LeanPool_CorlessNilpotent_Matrix
set_option autoImplicit true
@[expose] public section
public section
open Polynomial Matrix
open Corless

theorem Corless.T_nilpotent_iff {u : ℕ → ℂ} {m : ℕ}
    (hu : ∀ i, i + 1 < m → u i = 1 ∨ u i = Complex.I) (hm : 1 ≤ m) :
    IsNilpotent (T m u) ↔
      ∃ k, m = 2 ^ (k + 1) - 1 ∧ Fam k (fun i => entrySign (u i)) := by sorry
