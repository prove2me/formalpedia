-- Prove2me | Theorems.Thm_Erdos338Proof_nsmul_add_stab
-- name    : Erdos338Proof.nsmul_add_stab
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:57:32.682141+00:00
-- url     : https://prove2.me/theorems/83a86677-99bc-5445-afe5-1131d15686a2
-- title:
--   Erdos338 Proof: nsmul add stab
-- statement:
--   `h • (s + H) = h • s + H` when `H + H = H`.
--
--   Source: https://github.com/veljjanoski/erdos338-palomar/blob/a699263d0f7cdce0e5b3026bce86eab30973d0f8/Erdos338/Covering.lean#L25-L32
-- source:
--   https://github.com/veljjanoski/erdos338-palomar/blob/a699263d0f7cdce0e5b3026bce86eab30973d0f8/Erdos338/Covering.lean#L25-L32

module
public import Mathlib
public import Definitions.Def_Erdos338_Kneser_Kneser
public import Definitions.Def_Erdos338_Covering
set_option autoImplicit true
@[expose] public section
public section
open Finset
open scoped Pointwise
open Erdos338Proof
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem Erdos338Proof.nsmul_add_stab (s H : Finset G) (hH : H + H = H) {h : ℕ} (hh : 1 ≤ h) :
    h • (s + H) = h • s + H := by sorry
