-- Prove2me | Theorems.Thm_Erdos287_construct_compatible_slopes_on_prescribed_edges
-- name    : Erdos287.construct_compatible_slopes_on_prescribed_edges
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T12:26:35.189797+00:00
-- url     : https://prove2.me/theorems/a671a507-a4ae-5988-b7c7-e24c48c2d711
-- title:
--   Compatible affine slopes on designated pairs with prescribed congruences
-- statement:
--   Let $E$ be a finite set of oriented pairs $(i,j)$. Give each vertex an integer position $z_i$ and an integer base intercept $b_i$. On each edge let $\Delta_e=z_j-z_i>0$ and $d_e=b_j-b_i\ne0$, with $d_e\mid b_i$. Suppose $\Delta_e d_f\ne\Delta_f d_e$ for distinct edges. For any $K>0$ one can take arbitrarily large positive multiples $A,C$ of $K$ such that on every edge the difference $C\Delta_e+d_e$ is positive and divides $a_i=A+Cz_i+b_i$. The slopes preserve the base residues modulo $K$.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287.

import Mathlib

theorem Erdos287.construct_compatible_slopes_on_prescribed_edges (E : Finset (ℕ × ℕ)) (z b : ℕ → ℤ) (K R T : ℕ)
    (hK : 0 < K)
    (hedge : ∀ e ∈ E, z e.1 < z e.2 ∧ b e.2 ≠ b e.1 ∧ (b e.2 - b e.1) ∣ b e.1)
    (hdet : ∀ e ∈ E, ∀ f ∈ E, e ≠ f →
      (z e.2 - z e.1) * (b f.2 - b f.1) ≠ (z f.2 - z f.1) * (b e.2 - b e.1)) :
    ∃ A C : ℤ, (R : ℤ) < A ∧ (T : ℤ) < C ∧ (K : ℤ) ∣ A ∧ (K : ℤ) ∣ C ∧
      ∀ e ∈ E, 0 < C * (z e.2 - z e.1) + (b e.2 - b e.1) ∧
        (C * (z e.2 - z e.1) + (b e.2 - b e.1)) ∣ A + C * z e.1 + b e.1 := by sorry
