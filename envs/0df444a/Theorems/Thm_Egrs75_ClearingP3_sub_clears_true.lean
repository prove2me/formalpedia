-- Prove2me | Theorems.Thm_Egrs75_ClearingP3_sub_clears_true
-- name    : Egrs75.ClearingP3.sub_clears_true
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:30:25.4513+00:00
-- url     : https://prove2.me/theorems/101d1cf5-4ce6-47f1-8163-5beb874a2251
-- title:
--   Clearing P3: sub clears true
-- statement:
--   **P3 — EGRS75 SUBTRACT branch, TRUE form (`sub_clears_true`) — KERNEL-CLEAN modulo
--   the single floor residual.**  This is the maximally-honest primitive: it states EXACTLY
--   what the SUBTRACT move delivers and proves all of it except the one genuinely-undeliverable
--   floor atom.
--
--   For distinct odd primes `p q`, a `LowDigits p` number `n` (`n ≠ 0`), with the subtract
--   amount `S = (p^m+1)/2` (`m = lowPDigitIndex p n`) fitting under the base-`q` tail at the
--   top bad index (`S ≤ n % q^j`, `j = topBadIndex q n`), the result `n' = n - S` is
--
--     * `LowDigits p`                          (the hard base-`p` borrow — KERNEL-CLEAN), and
--     * good at every base-`q` index `> j`     (frozen high block — KERNEL-CLEAN).
--
--   These two are the complete TRUE content of the subtract branch and are proved with NO
--   `sorry`.  (NOTE the strict `j < idx`: digit `j` is FROZEN — equal to `n`'s bad digit — so
--   the subtract branch does NOT clear it; that is the ADD branch's job.)
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/SubtractBranch.lean#L430-L440
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/SubtractBranch.lean#L430-L440

module
public import Definitions.Def_LeanPool_Egrs75_DigitVector
public import Definitions.Def_LeanPool_Egrs75_DigitAtToolkit
public import Mathlib.Data.Nat.Factorization.Defs
public import Definitions.Def_LeanPool_Egrs75_RoundUp
public import Definitions.Def_LeanPool_Egrs75_SubtractBranch
set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.ClearingP3
open Nat
open Egrs75
open Egrs75.LeafInduction
open Egrs75.RepairDV
open Egrs75.RepairPaperfaithful

theorem Egrs75.ClearingP3.sub_clears_true {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpo : Odd p)
    {N n : ℕ} (hpn : LowDigits p n) (hNn : N < n) (hbad : 0 < badCountQ q n)
    (hST : (p ^ (lowPDigitIndex p n) + 1) / 2 ≤ n % q ^ (topBadIndex q n)) :
    LowDigits p (n - (p ^ (lowPDigitIndex p n) + 1) / 2) ∧
      (∀ idx, topBadIndex q n < idx →
        ¬ BadAt q idx (n - (p ^ (lowPDigitIndex p n) + 1) / 2)) := by sorry
