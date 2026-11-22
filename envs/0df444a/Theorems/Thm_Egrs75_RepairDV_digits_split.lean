-- Prove2me | Theorems.Thm_Egrs75_RepairDV_digits_split
-- name    : Egrs75.RepairDV.digits_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:27:11.587564+00:00
-- url     : https://prove2.me/theorems/7f170bdc-a266-4599-a73b-20134e77ffd6
-- title:
--   Repair DV: digits split
-- statement:
--   Base-`q` digit list of `Lo + q^k · Hi` is `digits Lo ++ zeros ++ digits Hi`,
--   for `Lo < q^k`, `Hi > 0`, `q ≥ 2`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/DigitVector.lean#L84-L89
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/DigitVector.lean#L84-L89

module
public import Definitions.Def_LeanPool_Egrs75_LeafInduction
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.Digits.Lemmas
public import Definitions.Def_LeanPool_Egrs75_DigitVector
set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.RepairDV
open Nat
open Egrs75
open Egrs75.LeafInduction

theorem Egrs75.RepairDV.digits_split {q k Lo Hi : ℕ} (hq : 1 < q) (hLo : Lo < q ^ k) (hHi : 0 < Hi) :
    Nat.digits q (Lo + q ^ k * Hi) =
      Nat.digits q Lo ++ List.replicate (k - (Nat.digits q Lo).length) 0 ++ Nat.digits q Hi := by sorry
