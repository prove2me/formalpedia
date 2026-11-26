-- Prove2me | Theorems.Thm_AlonTarsi_degree_outExp
-- name    : AlonTarsi.degree_outExp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:12:28.636272+00:00
-- url     : https://prove2.me/theorems/d4768b3c-2482-4b5c-8e79-d1ba77430246
-- title:
--   Alon Tarsi: degree out Exp
-- statement:
--   The Alon Tarsi construction uses the degree out Exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/AlonTarsiLib/GraphPolynomial.lean#L45-L49
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/AlonTarsiLib/GraphPolynomial.lean#L45-L49

module
public import Mathlib
public import Definitions.Def_AlonTarsiLib_GraphPolynomial
set_option autoImplicit true
@[expose] public section
public section
open Finset MvPolynomial
open AlonTarsi
variable {V : Type*}

theorem AlonTarsi.degree_outExp (A : Finset (V × V)) : (outExp A).degree = #A := by sorry
