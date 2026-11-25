-- Prove2me | Theorems.Thm_ConjCoord_lemma3
-- name    : ConjCoord.lemma3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:56:48.5658+00:00
-- url     : https://prove2.me/theorems/e0902fa6-cce4-445f-a484-d0778de860e1
-- title:
--   Conj Coord: lemma3
-- statement:
--   **Lemma 3**, combinatorial part: for `p ≡ 5 (mod 16)`, `r₃(p) = 3 r_{1,2,2}(p)` and
--   `r₃(2p) = 6 r_{1,2,4}(p)`. With Gauss's `r₃(m) = 12 h(-4m)` these are `r_{1,2,2}(p) = 4 h(-4p)`
--   and `r_{1,2,4}(p) = 2 h(-8p)`.
--
--   Source: https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/Solution.lean#L61-L63
-- source:
--   https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/Solution.lean#L61-L63

module
public import Definitions.Def_ConjCoord
public import Definitions.Def_ConjCoord_Solution
public import Theorems.Thm_ConjCoord_Proof_lemma3

set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord

theorem ConjCoord.lemma3 {p : ℕ} (hp : p % 16 = 5) :
    r3 p = 3 * reps 1 2 2 p ∧ r3 (2 * p) = 6 * reps 1 2 4 p := by sorry
