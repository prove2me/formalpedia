-- Prove2me | Theorems.Thm_AlonTarsi_eval_graphPoly
-- name    : AlonTarsi.eval_graphPoly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:12:43.000861+00:00
-- url     : https://prove2.me/theorems/18a338bc-bf51-50b1-816b-e92e82c3f51d
-- title:
--   Alon Tarsi: eval graph Poly
-- statement:
--   The Alon Tarsi construction uses the eval graph Poly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/AlonTarsiLib/GraphPolynomial.lean#L59-L61
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/AlonTarsiLib/GraphPolynomial.lean#L59-L61

module
public import Mathlib
public import Definitions.Def_AlonTarsiLib_GraphPolynomial
set_option autoImplicit true
@[expose] public section
public section
open Finset MvPolynomial
open AlonTarsi
variable {V : Type*}

theorem AlonTarsi.eval_graphPoly (A : Finset (V × V)) (x : V → ℤ) :
    eval x (graphPoly A) = ∏ a ∈ A, (x a.1 - x a.2) := by sorry
