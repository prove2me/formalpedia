-- Prove2me | Theorems.Thm_Egrs75_ClearingP2_add_U_lowDigits_p
-- name    : Egrs75.ClearingP2.add_U_lowDigits_p
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:28:06.066275+00:00
-- url     : https://prove2.me/theorems/6038bce4-e889-4fdc-8adf-31bfd3007529
-- title:
--   Clearing P2: add U low Digits p
-- statement:
--   **Base-`p` safety of `n + U` (KERNEL-CLEAN).**  Let `m` be the lowest nonzero
--   base-`p` digit index of `n` (`p^m ∣ n`).  If `U < p^m`, `U` and `n` are both
--   `LowDigits p`, and `n > 0`, then `n + U` is `LowDigits p`.
--
--   Proof.  `p^m ∣ n` gives `n = p^m · (n / p^m)`, so `n + U = U + p^m · (n / p^m)` with
--   `U < p^m`; the high block `n / p^m` is `LowDigits p` (`lowDigits_div_pow`) and `> 0`
--   (since `n > 0` forces `n ≥ p^m`), so `lowDigits_disjoint_add` applies — adding the
--   disjoint-support correction creates no oversized base-`p` digit.  This is the EGRS
--   "`U < p^m` keeps the base-`p` digits small" step.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/AddBranch.lean#L104-L121
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/AddBranch.lean#L104-L121

module
public import Definitions.Def_LeanPool_Egrs75_Defs
public import Definitions.Def_LeanPool_Egrs75_DigitAtToolkit
public import Definitions.Def_LeanPool_Egrs75_DigitVector
public import Definitions.Def_LeanPool_Egrs75_RoundUp
public import Definitions.Def_LeanPool_Egrs75_AddBranch
set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.ClearingP2
open Nat
open Egrs75
open Egrs75.LeafInduction
open Egrs75.RepairDV
open Egrs75.RepairPaperfaithful

theorem Egrs75.ClearingP2.add_U_lowDigits_p {p : ℕ} (hp : 2 ≤ p) {n m U : ℕ}
    (hpn : LowDigits p n) (hpU : LowDigits p U) (hUlt : U < p ^ m)
    (hm : n % p ^ m = 0) (hnpos : 0 < n) : LowDigits p (n + U) := by sorry
