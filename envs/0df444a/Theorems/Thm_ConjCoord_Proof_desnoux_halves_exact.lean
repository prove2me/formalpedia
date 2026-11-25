-- Prove2me | Theorems.Thm_ConjCoord_Proof_desnoux_halves_exact
-- name    : ConjCoord.Proof.desnoux_halves_exact
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:53:13.707542+00:00
-- url     : https://prove2.me/theorems/d631f08c-00ff-4991-98f6-1f65a7965016
-- title:
--   Proof: desnoux halves exact
-- statement:
--   **The halves in Desnoux's formula are exact.** For `p ≡ 5 (mod 16)`, any solutions of
--   `R² - p S₀² = 1` and `R'² - 2p S₀'² = 1` have `S₀` and `S₀'` even, so the integer quotients `S₀ / 2`
--   and `S₀' / 2` are the halves `S/2` and `S'/2` of Desnoux's Theorem B.
--
--   Source: https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/ConjCoord/Main.lean#L263-L267
-- source:
--   https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/ConjCoord/Main.lean#L263-L267

module
public import Definitions.Def_ConjCoord_Compute
public import Definitions.Def_ConjCoord_TwoSquares
public import Definitions.Def_ConjCoord_Main
set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord ConjCoord.Proof

theorem ConjCoord.Proof.desnoux_halves_exact {p : ℕ} (h5 : p % 16 = 5) {R S₀ R' S₀' : ℤ}
    (hPell : R ^ 2 - (p : ℤ) * S₀ ^ 2 = 1) (hPell' : R' ^ 2 - 2 * (p : ℤ) * S₀' ^ 2 = 1) :
    2 * (S₀ / 2) = S₀ ∧ 2 * (S₀' / 2) = S₀' := by sorry
