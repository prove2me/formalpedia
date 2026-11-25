-- Prove2me | Theorems.Thm_ConjCoord_phi_eq
-- name    : ConjCoord.phi_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:55:44.240898+00:00
-- url     : https://prove2.me/theorems/64a1d39c-c01d-4d71-a0c5-0d71141518fc
-- title:
--   Conj Coord: phi eq
-- statement:
--   The coefficients of `Φ = 4 θ(1) T`: `Φ(n) = 4 (T(n) + ∑_{k ≥ 1} 2 T(n - k²))`.
--
--   Source: https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/Solution.lean#L24-L27
-- source:
--   https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/Solution.lean#L24-L27

module
public import Definitions.Def_ConjCoord
public import Definitions.Def_ConjCoord_Solution
public import Theorems.Thm_ConjCoord_Proof_phi_eq

set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord

theorem ConjCoord.phi_eq (n : ℕ) :
    phi n = 4 * (tCoeff n + ∑ k ∈ range n,
      2 * (if (k + 1) ^ 2 ≤ n then tCoeff (n - (k + 1) ^ 2) else 0)) := by sorry
