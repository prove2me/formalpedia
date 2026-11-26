-- Prove2me | Theorems.Thm_AlonTarsi_sum_single_apply
-- name    : AlonTarsi.sum_single_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:12:25.870334+00:00
-- url     : https://prove2.me/theorems/042b065b-c870-4931-bea0-f508f2724aaf
-- title:
--   Alon Tarsi: sum single apply
-- statement:
--   The Alon Tarsi construction uses the sum single apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/AlonTarsiLib/GraphPolynomial.lean#L35-L39
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/AlonTarsiLib/GraphPolynomial.lean#L35-L39

module
public import Mathlib
public import Definitions.Def_AlonTarsiLib_GraphPolynomial
set_option autoImplicit true
@[expose] public section
public section
open Finset MvPolynomial
open AlonTarsi
variable {V : Type*}

theorem AlonTarsi.sum_single_apply [DecidableEq V] (s : Finset (V × V)) (g : V × V → V) (v : V) :
    (∑ a ∈ s, Finsupp.single (g a) 1 : V →₀ ℕ) v = #{a ∈ s | g a = v} := by sorry
