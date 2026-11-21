-- Prove2me | Theorems.Thm_Corless_det_CM_succ_succ
-- name    : Corless.det_CM_succ_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:41:51.557299+00:00
-- url     : https://prove2.me/theorems/f1ccdce5-7d4a-41bd-837a-f59e07d8618e
-- title:
--   Corless: det CM succ succ
-- statement:
--   Expansion along the first column, then along the first row of the second minor.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CorlessNilpotent/Matrix.lean#L52-L106
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CorlessNilpotent/Matrix.lean#L52-L106

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

theorem Corless.det_CM_succ_succ (m : ℕ) (u : ℕ → ℂ) :
    (CM (m + 2) u).det = X * (CM (m + 1) (fun i => u (i + 1))).det
      + C (u 0 ^ 2) * (CM m (fun i => u (i + 2))).det := by sorry
