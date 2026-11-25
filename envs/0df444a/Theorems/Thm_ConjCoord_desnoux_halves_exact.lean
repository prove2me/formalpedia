-- Prove2me | Theorems.Thm_ConjCoord_desnoux_halves_exact
-- name    : ConjCoord.desnoux_halves_exact
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:58:03.808235+00:00
-- url     : https://prove2.me/theorems/4b61bdd8-3279-557d-9899-e4ada29029b1
-- title:
--   Conj Coord: desnoux halves exact
-- statement:
--   **The halves in Desnoux's formula are exact.** For `p ≡ 5 (mod 16)`, any solutions of
--   `R² - p S₀² = 1` and `R'² - 2p S₀'² = 1` have `S₀` and `S₀'` even, so the integer quotients `S₀ / 2`
--   and `S₀' / 2` are the halves `S/2` and `S'/2` of Desnoux's Theorem B.
--
--   Source: https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/Solution.lean#L133-L136
-- source:
--   https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/Solution.lean#L133-L136

module
public import Definitions.Def_ConjCoord
public import Definitions.Def_ConjCoord_Solution
public import Theorems.Thm_ConjCoord_Proof_desnoux_halves_exact

set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord

theorem ConjCoord.desnoux_halves_exact {p : ℕ} (h5 : p % 16 = 5) {R S₀ R' S₀' : ℤ}
    (hPell : R ^ 2 - (p : ℤ) * S₀ ^ 2 = 1) (hPell' : R' ^ 2 - 2 * (p : ℤ) * S₀' ^ 2 = 1) :
    2 * (S₀ / 2) = S₀ ∧ 2 * (S₀' / 2) = S₀' := by sorry
