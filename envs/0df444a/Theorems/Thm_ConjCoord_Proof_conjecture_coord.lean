-- Prove2me | Theorems.Thm_ConjCoord_Proof_conjecture_coord
-- name    : ConjCoord.Proof.conjecture_coord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:53:43.716797+00:00
-- url     : https://prove2.me/theorems/f6f0eea2-3760-45ba-8cc5-d20197bc08f6
-- title:
--   Proof: conjecture coord
-- statement:
--   **Corollary 2 (Conjecture 5.3 of Paper V).** If `V` is equivalent to
--   `h(-8p) - h(-4p) ≡ 8·[p ≡ 5 (mod 32)] (mod 16)` (Paper V, Theorem 5.2(iv), for
--   `V = (v_λ(u₁) ≥ 2)`), then `V` holds exactly when one and only one of `b ≡ ±6 (mod 16)` and
--   `p ≡ 21 (mod 32)` holds.
--
--   Source: https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/ConjCoord/Main.lean#L151-L183
-- source:
--   https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/ConjCoord/Main.lean#L151-L183

module
public import Definitions.Def_ConjCoord_Compute
public import Definitions.Def_ConjCoord_TwoSquares
public import Definitions.Def_ConjCoord_Main
set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord ConjCoord.Proof

theorem ConjCoord.Proof.conjecture_coord (S : SturmInput phi 512) {p : ℕ} (hp : p.Prime) (h5 : p % 16 = 5)
    {a b : ℤ} (hab : a ^ 2 + b ^ 2 = p) (hb : Even b) {h h' : ℕ}
    (hG : r3 p = 12 * h) (hG' : r3 (2 * p) = 12 * h') (V : Prop)
    (hV : V ↔ (h' : ℤ) - h ≡ 8 * (if p % 32 = 5 then 1 else 0) [ZMOD 16]) :
    V ↔ ((b % 16 = 6 ∨ b % 16 = 10) ↔ ¬ p % 32 = 21) := by sorry
