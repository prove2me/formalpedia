-- Prove2me | Theorems.Thm_AlonTarsi_totalDegree_graphPoly
-- name    : AlonTarsi.totalDegree_graphPoly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:12:41.000035+00:00
-- url     : https://prove2.me/theorems/3bac46a4-3a17-5311-8ea8-a611f1254df9
-- title:
--   Alon Tarsi: total Degree graph Poly
-- statement:
--   The Alon Tarsi construction uses the total Degree graph Poly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/AlonTarsiLib/GraphPolynomial.lean#L51-L57
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/AlonTarsiLib/GraphPolynomial.lean#L51-L57

module
public import Mathlib
public import Definitions.Def_AlonTarsiLib_GraphPolynomial
set_option autoImplicit true
@[expose] public section
public section
open Finset MvPolynomial
open AlonTarsi
variable {V : Type*}

theorem AlonTarsi.totalDegree_graphPoly (A : Finset (V × V)) : (graphPoly A).totalDegree ≤ #A := by sorry
