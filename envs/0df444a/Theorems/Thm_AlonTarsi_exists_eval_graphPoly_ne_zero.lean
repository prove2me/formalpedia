-- Prove2me | Theorems.Thm_AlonTarsi_exists_eval_graphPoly_ne_zero
-- name    : AlonTarsi.exists_eval_graphPoly_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:23:17.0743+00:00
-- url     : https://prove2.me/theorems/612433c0-b6a4-4141-adc4-b93152ca335c
-- title:
--   Alon Tarsi: exists eval graph Poly ne zero
-- statement:
--   **Alon–Tarsi via the Combinatorial Nullstellensatz.** If the signed number of Eulerian
--   subsets of `A` is nonzero, then from any sets `S v` larger than the out-degrees one can pick
--   values separating the endpoints of every arc.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/AlonTarsiLib/GraphPolynomial.lean#L119-L134
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/AlonTarsiLib/GraphPolynomial.lean#L119-L134

module
public import Mathlib
public import Definitions.Def_AlonTarsiLib_GraphPolynomial
set_option autoImplicit true
@[expose] public section
public section
open Finset MvPolynomial
open AlonTarsi
variable {V : Type*}

theorem AlonTarsi.exists_eval_graphPoly_ne_zero [DecidableEq V] [Fintype V] (A : Finset (V × V))
    (hA : ∑ t ∈ A.powerset with (∀ v, #{p ∈ t | p.1 = v} = #{p ∈ t | p.2 = v}),
      (-1 : ℤ) ^ #t ≠ 0)
    (S : V → Finset ℤ) (hS : ∀ v, #{a ∈ A | a.1 = v} < #(S v)) :
    ∃ x : V → ℤ, (∀ v, x v ∈ S v) ∧ ∀ a ∈ A, x a.1 ≠ x a.2 := by sorry
