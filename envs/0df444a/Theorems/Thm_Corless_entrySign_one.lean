-- Prove2me | Theorems.Thm_Corless_entrySign_one
-- name    : Corless.entrySign_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:41:43.779842+00:00
-- url     : https://prove2.me/theorems/ad3caecf-2231-4c42-ac13-ae68e8e209d1
-- title:
--   Corless: entry Sign one
-- statement:
--   The Corless construction uses the entry Sign one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CorlessNilpotent/Matrix.lean#L207-L207
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CorlessNilpotent/Matrix.lean#L207-L207

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

theorem Corless.entrySign_one : entrySign 1 = 1 := by sorry
