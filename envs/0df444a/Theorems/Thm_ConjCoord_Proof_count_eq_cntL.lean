-- Prove2me | Theorems.Thm_ConjCoord_Proof_count_eq_cntL
-- name    : ConjCoord.Proof.count_eq_cntL
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:45:19.061035+00:00
-- url     : https://prove2.me/theorems/3a46e403-a96c-57d8-aa34-55ca60bff70f
-- title:
--   Proof: count eq cnt L
-- statement:
--   The box count equals the computed count.
--
--   Source: https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/ConjCoord/Compute.lean#L110-L194
-- source:
--   https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/ConjCoord/Compute.lean#L110-L194

module
public import Definitions.Def_ConjCoord_Defs
public import Definitions.Def_ConjCoord_Compute
set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord ConjCoord.Proof

theorem ConjCoord.Proof.count_eq_cntL (a b c n : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (P : ℤ → ℤ → Prop) [DecidableRel P] (Q : ℕ → ℕ → Bool)
    (hPQ : ∀ x y, P x y ↔ Q x.natAbs y.natAbs = true) :
    ((box3 n).filter fun v =>
        (a : ℤ) * v.1 ^ 2 + b * v.2.1 ^ 2 + c * v.2.2 ^ 2 = n ∧ P v.1 v.2.1).card =
      cntL a b c n Q := by sorry
