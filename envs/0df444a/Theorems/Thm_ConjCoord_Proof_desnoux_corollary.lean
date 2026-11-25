-- Prove2me | Theorems.Thm_ConjCoord_Proof_desnoux_corollary
-- name    : ConjCoord.Proof.desnoux_corollary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:54:10.557744+00:00
-- url     : https://prove2.me/theorems/a3f3d7a0-43ee-46b5-bd43-3f53e98d8604
-- title:
--   Proof: desnoux corollary
-- statement:
--   **Corollary 7 (with Desnoux).** Let `(R, S₀)` and `(R', S₀')` solve the Pell equations
--   `R² - p S₀² = 1` and `R'² - 2p S₀'² = 1` (Desnoux takes the least positive solutions; the corollary
--   holds for any). The integer quotients `S₀ / 2` and `S₀' / 2` are then the exact halves `S/2` and
--   `S'/2` (first two conjuncts, from `desnoux_halves_exact`), so the hypothesis `hD` is Desnoux's
--   Theorem B, §6, for `p ≡ 5 (mod 8)`,
--   `h(-4p) - c₂ R (S/2) h⁺(p) + h(-8p) - 17 R' (S'/2) h⁺(2p) ≡ 32·[p ≡ 5, 29 (mod 32)] (mod 64)`,
--   and the conclusion is
--   `c₂ R (S/2) h⁺(p) + 17 R' (S'/2) h⁺(2p) ≡ 2 h(-4p) + 8 A (mod 16)`.
--
--   Source: https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/ConjCoord/Main.lean#L277-L288
-- source:
--   https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/ConjCoord/Main.lean#L277-L288

module
public import Definitions.Def_ConjCoord_Compute
public import Definitions.Def_ConjCoord_TwoSquares
public import Definitions.Def_ConjCoord_Main
set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord ConjCoord.Proof

theorem ConjCoord.Proof.desnoux_corollary (S : SturmInput phi 512) {p : ℕ} (hp : p.Prime) (h5 : p % 16 = 5)
    {a b : ℤ} (hab : a ^ 2 + b ^ 2 = p) (hb : Even b) {h h' : ℕ}
    (hG : r3 p = 12 * h) (hG' : r3 (2 * p) = 12 * h') (c₂ R S₀ R' S₀' hplus hplus2 : ℤ)
    (hPell : R ^ 2 - (p : ℤ) * S₀ ^ 2 = 1) (hPell' : R' ^ 2 - 2 * (p : ℤ) * S₀' ^ 2 = 1)
    (hD : (h : ℤ) - c₂ * R * (S₀ / 2) * hplus + h' - 17 * R' * (S₀' / 2) * hplus2 ≡
      32 * (if p % 32 = 5 ∨ p % 32 = 29 then 1 else 0) [ZMOD 64]) :
    2 * (S₀ / 2) = S₀ ∧ 2 * (S₀' / 2) = S₀' ∧
      c₂ * R * (S₀ / 2) * hplus + 17 * R' * (S₀' / 2) * hplus2 ≡ 2 * h + 8 * octA b [ZMOD 16] := by sorry
