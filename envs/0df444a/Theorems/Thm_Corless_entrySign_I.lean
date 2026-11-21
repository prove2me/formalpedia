-- Prove2me | Theorems.Thm_Corless_entrySign_I
-- name    : Corless.entrySign_I
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:41:43.382418+00:00
-- url     : https://prove2.me/theorems/0b2b74d3-d1c4-4c6e-a3d5-e58a8da3c8c7
-- title:
--   Corless: entry Sign I
-- statement:
--   The Corless construction uses the entry Sign I property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CorlessNilpotent/Matrix.lean#L209-L209
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CorlessNilpotent/Matrix.lean#L209-L209

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

theorem Corless.entrySign_I : entrySign Complex.I = -1 := by sorry
