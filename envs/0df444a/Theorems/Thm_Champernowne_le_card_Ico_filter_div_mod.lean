-- Prove2me | Theorems.Thm_Champernowne_le_card_Ico_filter_div_mod
-- name    : Champernowne.le_card_Ico_filter_div_mod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:37:36.383374+00:00
-- url     : https://prove2.me/theorems/1d580e04-d0a4-4eb2-ba94-ccd0fb0d0e23
-- title:
--   Champernowne: le card Ico filter div mod
-- statement:
--   Lower bound for periodic counting: over `[A, A + t)` with a left
--   endpoint divisible by `p * q`, the value `n / p % q` hits a fixed `d < q`
--   at least `t / (p·q) · p` times — `p` hits in each complete period `p·q`.
--   Proved directly by injecting `range (t/(p·q)) ×ˢ range p`; the main proof
--   never needs the exact count (`card_Ico_filter_div_mod`,
--   `CountExtras.lean`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/DigitCount.lean#L44-L98
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/DigitCount.lean#L44-L98

module
public import Definitions.Def_LeanPool_Champernowne_Count
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_Champernowne_DigitCount
set_option autoImplicit true
@[expose] public section
public section
open Champernowne

theorem Champernowne.le_card_Ico_filter_div_mod {A t p q d : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hd : d < q) (hA : p * q ∣ A) :
    t / (p * q) * p
      ≤ ((Finset.Ico A (A + t)).filter (fun n => n / p % q = d)).card := by sorry
