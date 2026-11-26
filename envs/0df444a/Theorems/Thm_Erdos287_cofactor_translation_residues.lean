-- Prove2me | Theorems.Thm_Erdos287_cofactor_translation_residues
-- name    : Erdos287.cofactor_translation_residues
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T11:38:47.052853+00:00
-- url     : https://prove2.me/theorems/fee8cd8c-0e4f-4faa-a230-6f17c1ddda81
-- title:
--   Polynomial residue test for translated prime-power cofactor patterns
-- statement:
--   Let a finite positive denominator set have reciprocal sum one. If the selected multiples of $p^e$ have cofactors $c+T$ for prime $p$, $e\ge1$ and $c>0$, the sum of the products of all but one of these cofactors vanishes modulo $p$. For any finite family $F$ of offset sets, each with size below $p$, the allowed translations for nonempty layers lie in a residue set of size at most $\sum_{T\in F}\max(|T|-1,0)$. The residue set is exactly the union of zeros of the cleared cofactor numerators for the nonempty patterns.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287.

import Mathlib

theorem Erdos287.cofactor_translation_residues (p : ℕ) (hp : p.Prime) :
  (∀ (D T : Finset ℕ) (e c : ℕ), 1 ≤ e → 0 < c →
    (∀ n ∈ D, 0 < n) → (∑ n ∈ D, (1 : ℚ) / n = 1) →
    T.image (fun d => (c + d) * p ^ e) = D.filter (fun n => p ^ e ∣ n) →
    (∑ a ∈ T, ∏ b ∈ T.erase a, ((c : ZMod p) + b)) = 0) ∧
  ∀ (F : Finset (Finset ℕ)), (∀ T ∈ F, T.card < p) →
    ∃ R : Finset (ZMod p),
      R.card ≤ ∑ T ∈ F, (T.card - 1) ∧
      (∀ x : ZMod p, x ∈ R ↔ ∃ T ∈ F, T.Nonempty ∧
        (∑ a ∈ T, ∏ b ∈ T.erase a, (x + (b : ZMod p))) = 0) ∧
      ∀ (D : Finset ℕ) (e c : ℕ), 1 ≤ e → 0 < c →
        (∀ n ∈ D, 0 < n) → (∑ n ∈ D, (1 : ℚ) / n = 1) →
        ∀ T ∈ F,
          T.image (fun d => (c + d) * p ^ e) = D.filter (fun n => p ^ e ∣ n) →
          T.Nonempty → (c : ZMod p) ∈ R := by sorry
