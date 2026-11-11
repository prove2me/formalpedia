-- Prove2me | Theorems.Thm_EqualSubsetSum_Faster_lemma_3_4
-- name    : EqualSubsetSum.Faster.lemma_3_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T23:26:29.918896+00:00
-- url     : https://prove2.me/theorems/09cd9d61-4aff-495c-b90c-78d291fdc49a
-- title:
--   Lemma 3.4 — equal sums in a translated cube
-- statement:
--   Let $y\in\mathbb Z^n$ and suppose every solution for $y$ has at least $s$ nonzero entries. Let $C$ be a translated cube with $v$ free coordinates. If $q\ge2$ distinct members of $C$ have the same weighted sum with respect to $y$, then
--   $$\binom q2 s\le v\left\lfloor \frac{q^2}{4}\right\rfloor .$$
--   Consequently the members of $C$ have pairwise distinct sums if $v<s$; at most two members share a sum if $2v<3s$; and at most $2s/(2s-v)$ members share a sum if $v<2s$.
--
--   This is the source of distinct common sums in every layout of the paper.
--
--   Differences from the source:
--   - encoding: q ≥ 2 distinct members with the same sum → a finite set S of members with |S| = q ≥ 2 on which the weighted sum is constant; reason: a set of distinct members is a Finset
--   - encoding: at most 2s/(2s − v) members share a sum → (|S| : ℝ) ≤ 2s/(2s − v) for every set S of members with a common sum; reason: the bound is a real number
-- source:
--   Cheshm Jahan, Keshavarz Hedayati, Safari, Shahrezaei, Faster Equal-Subset-Sum via Truncated Inclusion–Exclusion, STOC 2027 submission (manuscript, sha256 7ad8c8b2…61dacd1), p. 18, Lemma 3.4

import Mathlib
import Definitions.Def_EqualSubsetSum_Faster_Problem
import Definitions.Def_EqualSubsetSum_Faster_Cube

namespace EqualSubsetSum.Faster

/-- Lemma 3.4 (p. 18). Let every solution for `y` have at least `s` nonzero entries and let `C`
be a translated cube with `v` free coordinates. If `q ≥ 2` distinct members of `C` have the same
weighted sum, then `(q choose 2) s ≤ v ⌊q²/4⌋`. Consequently the members have pairwise distinct
sums if `v < s`, at most two members share a sum if `2v < 3s`, and at most `2s/(2s - v)` members
share a sum if `v < 2s`. -/
theorem lemma_3_4 {n : ℕ} (y : Fin n → ℤ) (s : ℕ)
    (hs : ∀ d, IsSolution y d → s ≤ (supp d).card)
    (C : Fin n → Finset ℤ) (hC : IsTranslatedCube C) :
    (∀ S ⊆ cubeMembers C, 2 ≤ S.card →
        (∀ u ∈ S, ∀ u' ∈ S, weightedSum u y = weightedSum u' y) →
        S.card.choose 2 * s ≤ freeCoords C * (S.card ^ 2 / 4)) ∧
    (freeCoords C < s → ∀ u ∈ cubeMembers C, ∀ u' ∈ cubeMembers C,
        weightedSum u y = weightedSum u' y → u = u') ∧
    (2 * freeCoords C < 3 * s → ∀ S ⊆ cubeMembers C,
        (∀ u ∈ S, ∀ u' ∈ S, weightedSum u y = weightedSum u' y) → S.card ≤ 2) ∧
    (freeCoords C < 2 * s → ∀ S ⊆ cubeMembers C,
        (∀ u ∈ S, ∀ u' ∈ S, weightedSum u y = weightedSum u' y) →
        (S.card : ℝ) ≤ 2 * s / (2 * s - freeCoords C)) := by sorry

end EqualSubsetSum.Faster
