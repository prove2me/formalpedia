-- Prove2me | Theorems.Thm_Erdos287_endpoint_extremal_cofactor_layer_hits_joint_replacements
-- name    : Erdos287.endpoint_extremal_cofactor_layer_hits_joint_replacements
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-27T01:14:51.51498+00:00
-- url     : https://prove2.me/theorems/8b05a72c-6f24-4bc3-b940-9cc9b3ad8684
-- title:
--   Joint endpoint trimming constrains the shared prime-power layer
-- statement:
--   When both endpoints are $cp^e$ and $dp^e$, the selected cofactors must pass the carry test. They must also meet each subset of the strict interior cofactors having reciprocal sum $1/c+1/d$.
-- source:
--   Erdős Problem 287. The extremal endpoint cover reduction.

import Mathlib

theorem Erdos287.endpoint_extremal_cofactor_layer_hits_joint_replacements (D : Finset ℕ) (p e c d L j : ℕ) (hp : p.Prime) (he : 1 ≤ e)
    (hcd : c < d) (hLp : p ^ j ∣ L) :
    let q := p ^ e
    let m := c * q
    let M := d * q
    let C := (Finset.Icc c d).filter (fun a => a * q ∈ D)
    1 < m → m ∈ D → M ∈ D → D ⊆ Finset.Icc m M →
    (∀ x, m ≤ x → x + 1 ≤ M → x ∈ D ∨ x + 1 ∈ D) →
    (∑ n ∈ D, (1 : ℚ) / n = 1) →
    (∀ (a b : ℕ) (F : Finset ℕ), 1 < a → a ∈ F → b ∈ F →
      F ⊆ Finset.Icc a b → (∀ x, a ≤ x → x + 1 ≤ b → x ∈ F ∨ x + 1 ∈ F) →
      (∑ n ∈ F, (1 : ℚ) / n = 1) → M ≤ b ∧ (b = M → a ≤ m)) →
    (∀ a ∈ Finset.Icc c d, a ∣ L) →
    c ∈ C ∧ d ∈ C ∧ p ^ (j + 1) ∣ (∑ a ∈ C, L / a) ∧
      ∀ A ⊆ Finset.Ioo c d, (∑ a ∈ A, (1 : ℚ) / a = 1 / (c : ℚ) + 1 / (d : ℚ)) →
        ∃ a ∈ A, a ∈ C := by sorry
