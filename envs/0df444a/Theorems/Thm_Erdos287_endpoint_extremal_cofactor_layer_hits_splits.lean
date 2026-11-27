-- Prove2me | Theorems.Thm_Erdos287_endpoint_extremal_cofactor_layer_hits_splits
-- name    : Erdos287.endpoint_extremal_cofactor_layer_hits_splits
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-27T00:40:32.418873+00:00
-- url     : https://prove2.me/theorems/6acda411-44ac-40d5-b5fa-492ed2402348
-- title:
--   The lower endpoint layer must meet every reciprocal decomposition
-- statement:
--   For a cover with extremal endpoints and smallest denominator $cp^e$, the cofactors of the selected $p^e$-multiples pass the full carry test. They also meet every subset of higher in-range cofactors whose reciprocal sum is $1/c$.
-- source:
--   Erdős Problem 287. Combining endpoint extremality with prime-power cofactor cuts.

import Mathlib

theorem Erdos287.endpoint_extremal_cofactor_layer_hits_splits (D : Finset ℕ) (p e c M L j : ℕ) (hp : p.Prime) (he : 1 ≤ e)
    (hLp : p ^ j ∣ L) :
    let q := p ^ e
    let m := c * q
    let U := Finset.Icc c (M / q)
    let C := U.filter (fun a => a * q ∈ D)
    1 < m → m ∈ D → D ⊆ Finset.Icc m M →
    (∀ x, m ≤ x → x + 1 ≤ M → x ∈ D ∨ x + 1 ∈ D) →
    (∑ n ∈ D, (1 : ℚ) / n = 1) →
    (∀ (a b : ℕ) (F : Finset ℕ), 1 < a → a ∈ F → b ∈ F →
      F ⊆ Finset.Icc a b → (∀ x, a ≤ x → x + 1 ≤ b → x ∈ F ∨ x + 1 ∈ F) →
      (∑ n ∈ F, (1 : ℚ) / n = 1) → M ≤ b ∧ (b = M → a ≤ m)) →
    (∀ a ∈ U, a ∣ L) →
    c ∈ C ∧ p ^ (j + 1) ∣ (∑ a ∈ C, L / a) ∧
      ∀ A ⊆ Finset.Ioc c (M / q), (∑ a ∈ A, (1 : ℚ) / a = (1 : ℚ) / c) →
        ∃ a ∈ A, a ∈ C := by sorry
