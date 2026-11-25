-- Prove2me | Theorems.Thm_ConjCoord_Proof_phi_eq
-- name    : ConjCoord.Proof.phi_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:51:21.830752+00:00
-- url     : https://prove2.me/theorems/0d2bb881-1397-5d83-9f71-d8cf1bd058bd
-- title:
--   Proof: phi eq
-- statement:
--   `Φ = 4 θ(1) T` with `T = F₅ - 8 G θ(16)`, coefficientwise:
--   `Φ(n) = 4 (T(n) + ∑_{1 ≤ k} 2 T(n - k²))`.
--
--   Source: https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/ConjCoord/Main.lean#L48-L61
-- source:
--   https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/ConjCoord/Main.lean#L48-L61

module
public import Definitions.Def_ConjCoord_Compute
public import Definitions.Def_ConjCoord_TwoSquares
public import Definitions.Def_ConjCoord_Main
set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord ConjCoord.Proof

theorem ConjCoord.Proof.phi_eq (n : ℕ) :
    phi n = 4 * (tCoeff n + ∑ k ∈ range n,
      2 * (if (k + 1) ^ 2 ≤ n then tCoeff (n - (k + 1) ^ 2) else 0)) := by sorry
