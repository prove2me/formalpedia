-- Prove2me | Theorems.Thm_Erdos287_crt_compress_cofactor_sums_by_residue_counts
-- name    : Erdos287.crt_compress_cofactor_sums_by_residue_counts
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T17:38:52.70355+00:00
-- url     : https://prove2.me/theorems/9877e31a-0dba-445f-ad84-c0bc950887e8
-- title:
--   CRT count of cofactor sums with explicit residue bounds
-- statement:
--   Let finite nonnegative weights have total at most \(KQ\), where \(Q=\prod_i q_i\) and the \(q_i\) are pairwise coprime. For each modulus \(q_i\), the subset sums of the weights nonzero modulo \(q_i\) assume at most \(R_i\) residues. There are at most \((K+1)\prod_i R_i\) distinct nonempty subset sums, with a representative subset for every sum.
-- source:
--   Erdős #287, counting possible prime-layer cancellations.

import Mathlib
open Finset

theorem Erdos287.crt_compress_cofactor_sums_by_residue_counts (U I : Finset ℕ) (q w R : ℕ → ℕ) (K : ℕ)
    (hq : ∀ i ∈ I, 0 < q i)
    (hcop : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → (q i).Coprime (q j))
    (hbound : (∑ x ∈ U, w x) ≤ K * ∏ i ∈ I, q i)
    (hR : ∀ i ∈ I,
      ((U.filter (fun x => ¬ q i ∣ w x)).powerset.image
        (fun T => (∑ x ∈ T, w x) % q i)).card ≤ R i) :
    ∃ F : Finset (Finset ℕ),
      (∀ T ∈ F, T ⊆ U ∧ T.Nonempty) ∧
      (∀ T ⊆ U, T.Nonempty → ∃ V ∈ F, (∑ x ∈ V, w x) = ∑ x ∈ T, w x) ∧
      F.card ≤ (K + 1) * ∏ i ∈ I, R i := by sorry
