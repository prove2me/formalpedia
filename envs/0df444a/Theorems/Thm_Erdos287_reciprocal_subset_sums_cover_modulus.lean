-- Prove2me | Theorems.Thm_Erdos287_reciprocal_subset_sums_cover_modulus
-- name    : Erdos287.reciprocal_subset_sums_cover_modulus
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T13:09:37.66713+00:00
-- url     : https://prove2.me/theorems/b9c7592b-59d5-579d-9efd-7e9aca2b8ee0
-- title:
--   A finite Fourier criterion for modular reciprocal subset sums
-- statement:
--   Let $q>0$ and let $D$ consist of units modulo $q$ with $n\le M$, each with a distinct prime factor label at least $Y\ge2$. Write $C=2(\lfloor MR/q\rfloor+1)K$ and $E=\max(0,|D|-C)$. If $(\lfloor MR/q\rfloor+1)q<Y^{K+1}$ and $q\exp(-2(R/q)^2 E)<1$, then the modular reciprocal sums of subsets of $D$ cover every residue modulo $q$.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287.

import Mathlib

theorem Erdos287.reciprocal_subset_sums_cover_modulus (q : ℕ) [NeZero q] (D : Finset ℕ) (label : ℕ → ℕ)
    (M R Y K : ℕ) (t : ZMod q) (hY : 2 ≤ Y)
    (hD : ∀ n ∈ D, n ≤ M ∧ (label n).Prime ∧ Y ≤ label n ∧ label n ∣ n)
    (hinj : Set.InjOn label (↑D : Set ℕ))
    (hunit : ∀ n ∈ D, IsUnit (n : ZMod q))
    (hsize : (M * R / q + 1) * q < Y ^ (K + 1))
    (hsmall : (q : ℝ) * Real.exp
      (-2 * ((R : ℝ) / q) ^ 2 * ↑(D.card - 2 * (M * R / q + 1) * K)) < 1) :
    ∃ T ⊆ D, (∑ n ∈ T, (n : ZMod q)⁻¹) = t := by sorry
