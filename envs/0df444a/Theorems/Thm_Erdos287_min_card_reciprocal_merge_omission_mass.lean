-- Prove2me | Theorems.Thm_Erdos287_min_card_reciprocal_merge_omission_mass
-- name    : Erdos287.min_card_reciprocal_merge_omission_mass
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T23:48:29.030386+00:00
-- url     : https://prove2.me/theorems/897be301-36cf-49f9-b02d-b0c8b6eb52d2
-- title:
--   Transfer of omissions between disjoint reciprocal-merge bands
-- statement:
--   Let $1/a+1/b=1/c$ be a two-term identity with the stated separation conditions. For a finite set of scale parameters $t$, a minimum-cardinality exact pair cover with omitted $ct$ must omit a different integer within distance one of $at$ or $bt$. The stated inequalities bound both the number and the reciprocal mass of these omissions.
-- source:
--   Erdős Problem 287. Exact reciprocal fusion in a cardinality-minimal denominator set.

import Mathlib

theorem Erdos287.min_card_reciprocal_merge_omission_mass (D T : Finset ℕ) (m M l u : ℕ)
    (hm : m ∈ D) (hD : D ⊆ Finset.Icc m M)
    (hcover : ∀ x, m ≤ x → x + 1 ≤ M → x ∈ D ∨ x + 1 ∈ D)
    (hsum : ∑ n ∈ D, (1 : ℚ) / n = 1)
    (hmin : ∀ E : Finset ℕ, m ∈ E → E ⊆ Finset.Icc m M →
      (∀ x, m ≤ x → x + 1 ≤ M → x ∈ E ∨ x + 1 ∈ E) →
      (∑ n ∈ E, (1 : ℚ) / n = 1) → D.card ≤ E.card)
    (a b c : ℕ) (hA : 3 ≤ a) (hAB : a + 2 ≤ b) (hCA : c < a)
    (hidentity : (1 : ℚ) / a + 1 / b = 1 / c)
    (hl : 0 < l) (hsep : a * u + 2 < b * l)
    (hT : ∀ t ∈ T, l ≤ t ∧ t ≤ u ∧ m ≤ c * t ∧ b * t ≤ M) :
    let L := T.filter (fun t => c * t ∉ D)
    let H := (Finset.Icc m M).filter (fun n => n ∉ D ∧
      ((a * l ≤ n + 1 ∧ n ≤ a * u + 1) ∨
        (b * l ≤ n + 1 ∧ n ≤ b * u + 1)))
    L.card ≤ H.card ∧
      (∑ t ∈ L, (1 : ℚ) / ((b * t + 1 : ℕ) : ℚ)) ≤
        ∑ n ∈ H, (1 : ℚ) / n := by sorry
