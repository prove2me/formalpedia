-- Prove2me | Theorems.Thm_BitDFT_packed_signed_scale_identity
-- name    : BitDFT.packed_signed_scale_identity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T02:29:16.600995+00:00
-- url     : https://prove2.me/theorems/655801e8-572d-44a2-a87d-bf6caefbf337
-- title:
--   Scale a signed Kronecker-packed coordinate block
-- statement:
--   Let a block contain signed integer coordinates of magnitude at most 2^q, including the endpoint, with n at most 2^ell, ell at most q, and q at least 2. At base 2^(3q), multiplying the Kronecker-packed block by n is exactly the packed form of the coordinatewise products. Every scaled coordinate has magnitude strictly below half the base, so balanced digit unpacking recovers it without cross-digit carries.
-- source:
--   Signed-integer algebra and balanced-digit bound for the packed rescaling branch of BitDFT.rescale_output_machine.

import Definitions.Def_IntMul_HvdH_KronMul
import Mathlib.Tactic
set_option autoImplicit false
open IntMul IntMul.HvdH

theorem BitDFT.packed_signed_scale_identity (n q ell : ℕ) (hn : n ≤ 2^ell)
    (hell : ell ≤ q) (hq : 2 ≤ q)
    (xs : List ℤ) (hxs : ∀ x ∈ xs, x.natAbs ≤ 2^q) :
    (∀ x ∈ xs, ((n : ℤ) * x).natAbs < 2^(3*q-1)) ∧
      kpack (2^(3*q)) (xs.map (fun x => (n : ℤ) * x)) =
        (n : ℤ) * kpack (2^(3*q)) xs := by sorry
