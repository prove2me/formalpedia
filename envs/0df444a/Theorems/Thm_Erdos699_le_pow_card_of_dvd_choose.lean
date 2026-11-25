-- Prove2me | Theorems.Thm_Erdos699_le_pow_card_of_dvd_choose
-- name    : Erdos699.le_pow_card_of_dvd_choose
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:48:39.255441+00:00
-- url     : https://prove2.me/theorems/ec046dd1-659e-4bbe-98c6-681289290b88
-- title:
--   Erdos699: le pow card of dvd choose
-- statement:
--   A divisor `g` of `C(n, i)`, with `i ≤ n`, is at most `n ^ ω(g)`, because
--   `p ^ v_p(C(n, i)) ≤ n` for every prime `p` (Kummer).
--
--   Source: https://github.com/Paulee314/erdos699-lean/blob/814f545f5f6475786aa5a04e4e795a25cda3670c/Erdos699/Basic.lean#L81-L94
-- source:
--   https://github.com/Paulee314/erdos699-lean/blob/814f545f5f6475786aa5a04e4e795a25cda3670c/Erdos699/Basic.lean#L81-L94

module
public import Mathlib
public import Definitions.Def_Erdos699_Basic
set_option autoImplicit false
@[expose] public section
public section
open Erdos699

theorem Erdos699.le_pow_card_of_dvd_choose {g n i : ℕ} (hn : n ≠ 0) (hg : g ≠ 0) (hin : i ≤ n)
    (hdvd : g ∣ n.choose i) : g ≤ n ^ g.primeFactors.card := by sorry
