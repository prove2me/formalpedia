-- Prove2me | Theorems.Thm_Erdos287_variable_cofactors_force_affine_identity
-- name    : Erdos287.variable_cofactors_force_affine_identity
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T19:26:39.96414+00:00
-- url     : https://prove2.me/theorems/d9268ac5-2ca7-41e5-9505-3378c15740e6
-- title:
--   Changing cofactors in a narrow affine parameter window
-- statement:
--   Let $P(t)=at+b$ and $Q(t)=rt+s$. In a set of integer parameters of diameter at most $H$, assume $Q(t)\geq Y>2B$ and $B^2|as-br|H<Y(Y-2B)$. If at every parameter there are positive cofactors at most $B$ giving consecutive multiples of $P(t)$ and $Q(t)$, then either there are at most two parameters or one pair of cofactors gives an affine adjacent-multiple identity on the whole line.
-- source:
--   Erdős #287, common-window affine certificates with changing cofactors.

import Mathlib

theorem Erdos287.variable_cofactors_force_affine_identity (T : Finset ℤ) (a b r s Y H : ℤ) (B : ℕ)
    (hY : 2 * (B : ℤ) < Y)
    (hq : ∀ t ∈ T, Y ≤ r * t + s)
    (hwidth : ∀ t ∈ T, ∀ u ∈ T, |t - u| ≤ H)
    (hgap : (B : ℤ) ^ 2 * |a * s - b * r| * H < Y * (Y - 2 * (B : ℤ)))
    (hcert : ∀ t ∈ T, ∃ c d : ℕ, 0 < c ∧ 0 < d ∧ c ≤ B ∧ d ≤ B ∧
      |(c : ℤ) * (a * t + b) - (d : ℤ) * (r * t + s)| = 1) :
    T.card ≤ 2 ∨ ∃ c d : ℕ, 0 < c ∧ 0 < d ∧ c ≤ B ∧ d ≤ B ∧
      (c : ℤ) * a = (d : ℤ) * r ∧ |(c : ℤ) * b - (d : ℤ) * s| = 1 := by sorry
