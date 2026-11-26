-- Prove2me | Theorems.Thm_AlonTarsi_coeff_outExp_graphPoly
-- name    : AlonTarsi.coeff_outExp_graphPoly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:12:50.294639+00:00
-- url     : https://prove2.me/theorems/d6f9ef13-d048-50e6-a3d9-081a5b018b37
-- title:
--   Alon Tarsi: coeff out Exp graph Poly
-- statement:
--   The coefficient of the out-degree monomial in the graph polynomial is the signed number of
--   Eulerian subsets of `A`.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/AlonTarsiLib/GraphPolynomial.lean#L65-L114
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/AlonTarsiLib/GraphPolynomial.lean#L65-L114

module
public import Mathlib
public import Definitions.Def_AlonTarsiLib_GraphPolynomial
set_option autoImplicit true
@[expose] public section
public section
open Finset MvPolynomial
open AlonTarsi
variable {V : Type*}

theorem AlonTarsi.coeff_outExp_graphPoly [DecidableEq V] [Fintype V] (A : Finset (V × V)) :
    (graphPoly A).coeff (outExp A) =
      ∑ t ∈ A.powerset with (∀ v, #{p ∈ t | p.1 = v} = #{p ∈ t | p.2 = v}), (-1 : ℤ) ^ #t := by sorry
