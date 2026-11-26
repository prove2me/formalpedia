-- Prove2me | Theorems.Thm_AlonTarsi_outExp_apply
-- name    : AlonTarsi.outExp_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:12:29.2038+00:00
-- url     : https://prove2.me/theorems/350f0fc8-0e41-4281-8114-1e8fe6e7d902
-- title:
--   Alon Tarsi: out Exp apply
-- statement:
--   The Alon Tarsi construction uses the out Exp apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/AlonTarsiLib/GraphPolynomial.lean#L41-L43
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/AlonTarsiLib/GraphPolynomial.lean#L41-L43

module
public import Mathlib
public import Definitions.Def_AlonTarsiLib_GraphPolynomial
set_option autoImplicit true
@[expose] public section
public section
open Finset MvPolynomial
open AlonTarsi
variable {V : Type*}

theorem AlonTarsi.outExp_apply [DecidableEq V] (A : Finset (V × V)) (v : V) :
    outExp A v = #{a ∈ A | a.1 = v} := by sorry
