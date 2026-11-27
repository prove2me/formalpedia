-- Prove2me | Theorems.Thm_Erdos287_four_reciprocal_merge_bands_amplify_omissions
-- name    : Erdos287.four_reciprocal_merge_bands_amplify_omissions
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T23:54:10.932598+00:00
-- url     : https://prove2.me/theorems/4f5031bd-a4de-5a76-8b49-48ad9de0217a
-- title:
--   Four separated reciprocal-merge bands amplify omissions
-- statement:
--   In a minimum-cardinality exact pair cover, take scales $t$ in a common interval $[l,u]$ with $100u\le101l$. For those scales with $45045t$ omitted and all four reciprocal-merge input pairs inside the ambient interval, the upper band contains at least four times as many omitted denominators and at least $7/4$ times their reciprocal mass.
-- source:
--   Erdős Problem 287. Exact reciprocal fusion in a cardinality-minimal denominator set.

import Mathlib

theorem Erdos287.four_reciprocal_merge_bands_amplify_omissions (D T : Finset ℕ) (m M l u : ℕ)
    (hm : m ∈ D) (hD : D ⊆ Finset.Icc m M)
    (hcover : ∀ x, m ≤ x → x + 1 ≤ M → x ∈ D ∨ x + 1 ∈ D)
    (hsum : ∑ n ∈ D, (1 : ℚ) / n = 1)
    (hmin : ∀ E : Finset ℕ, m ∈ E → E ⊆ Finset.Icc m M →
      (∀ x, m ≤ x → x + 1 ≤ M → x ∈ E ∨ x + 1 ∈ E) →
      (∑ n ∈ E, (1 : ℚ) / n = 1) → D.card ≤ E.card)
    (hl : 0 < l) (hu : 100 * u ≤ 101 * l)
    (hT : ∀ t ∈ T, l ≤ t ∧ t ≤ u ∧ m ≤ 45045 * t ∧ 108108 * t ≤ M) :
    let L := T.filter (fun t => 45045 * t ∉ D)
    let R := (Finset.Icc m M).filter (fun n => n ∉ D ∧
      77220 * l ≤ n + 1 ∧ n ≤ 108108 * u + 1)
    4 * L.card ≤ R.card ∧
      (7 / 4 : ℚ) * (∑ t ∈ L, (1 : ℚ) / ((45045 * t : ℕ) : ℚ)) ≤
        ∑ n ∈ R, (1 : ℚ) / n := by sorry
