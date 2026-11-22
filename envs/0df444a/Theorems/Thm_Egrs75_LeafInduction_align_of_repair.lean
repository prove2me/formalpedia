-- Prove2me | Theorems.Thm_Egrs75_LeafInduction_align_of_repair
-- name    : Egrs75.LeafInduction.align_of_repair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:26:50.40291+00:00
-- url     : https://prove2.me/theorems/e50325ea-65e4-4bcc-8f4f-d80887b4b4ca
-- title:
--   Leaf Induction: align of repair
-- statement:
--   **Reduction (FULLY KERNEL-CLEAN).**  The repair step is taken here as an EXPLICIT
--   hypothesis `hrepair` (the abstract EGRS carry-control property), so this lemma proves
--   NOTHING unproven — it is the pure logical reduction "iterate a potential-decreasing,
--   `LowDigits p`-preserving, strictly-increasing repair until the base-`q` potential is
--   `0`, where `badCountQ_eq_zero_iff_lowDigits` certifies `LowDigits q`".
--
--   From a `LowDigits p` seed strictly above `N`, repeatedly applying `hrepair` drives the
--   base-`q` potential to `0`, yielding a number that is `> N`, `LowDigits p`, and
--   `LowDigits q`.  Strong induction on the potential `badCountQ q` of the running number.
--   KERNEL-CLEAN (no `sorry`, no axioms beyond propext/Classical.choice/Quot.sound);
--   `align_induction` supplies the concrete `hrepair := repair_step` (the one `sorry`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/LeafInduction.lean#L157-L178
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/LeafInduction.lean#L157-L178

module
public import Definitions.Def_LeanPool_Egrs75_Defs
public import Mathlib.Data.Finset.Attr
public import Definitions.Def_LeanPool_Egrs75_LeafInduction
set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.LeafInduction
open Nat
open Egrs75

theorem Egrs75.LeafInduction.align_of_repair {p q : ℕ} (N : ℕ)
    (hrepair : ∀ {n : ℕ}, LowDigits p n → 0 < badCountQ q n →
      ∃ n', n < n' ∧ LowDigits p n' ∧ badCountQ q n' < badCountQ q n)
    (seed : ℕ) (hseedN : N < seed) (hseedp : LowDigits p seed) :
    ∃ n, N < n ∧ LowDigits p n ∧ LowDigits q n := by sorry
