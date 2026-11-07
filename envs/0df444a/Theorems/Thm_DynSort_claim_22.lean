-- Prove2me | Theorems.Thm_DynSort_claim_22
-- name    : DynSort.claim_22
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:40:28.787196+00:00
-- url     : https://prove2.me/theorems/20ea1c52-d6c0-4c59-9beb-2887f8e3cefe
-- title:
--   Claim 22 — $\mathrm{cross}_z(A')\le4i^2$ for every subsequence $A'$ of a level-$i$ A-DST
-- statement:
--   Let $A$ be a level-$i$ A-DST whose components $D_j$ ($1\le j\le i$, with $D_1=A_1$) are hole-free sections satisfying the level-$j$ structural invariants, and let $A'$ be any subsequence of the values of the elements of $A$, read from left to right. Then for every threshold $z$,
--   $$\mathrm{cross}_z(A')\le 4i^2,$$
--   and if all values of $A'$ lie in an interval $I=[a,b]$ with $a\le b$, then
--   $$\mathrm{cost}(A')\le 4i^2\,(b-a).$$
--
--   With $A'$ the active elements and $i=d=O(\log n)$, this is the $O(\log^2 n)$ competitive ratio of Theorem 1.
--
--   Differences from the source:
--   - generalization: cost(A′) = O(i²)·|I| → cost(A′) ≤ 4i²·(b − a); reason: 4i² is the constant the crossing bound gives when integrated (proof, p.23); it implies O(i²)
--   - encoding: a level-i A-DST, elements in an interval I → components satisfying the invariants of their levels, hole-free, values of the stored elements, I = [a, b] with a ≤ b; reason: between updates the A-DST has no hole; with a > b no interval contains the elements
--   - encoding: elements are distinct reals (ties broken by infinitesimal perturbations, p.11) → elements of ℝ ×ₗ ℕ, a value and an identifier ordered lexicographically; reason: the identifier is the perturbation; every instance of the source is one of these
-- source:
--   Azar, Bhore, Dey, Panigrahi, Vardi, Zhang, Online and Fully-Dynamic Sorting, STOC 2027 submission (manuscript sha256 da7f0d5ef6191ccaa6c70faec62234592c6d108cd2357bda3e5b6dac010acf6c), Claim 22, p.23 (PDF p.25)

import Mathlib
import Definitions.Def_DynSort_cost
import Definitions.Def_DynSort_cross
import Definitions.Def_DynSort_Inv
import Definitions.Def_DynSort_ADST

namespace DynSort

/-- **Claim 22**, Y. Azar, S. Bhore, D. Dey, D. Panigrahi, O. Vardi, I. Zhang, *Online and Fully-Dynamic Sorting*,
STOC 2027 submission (manuscript sha256 da7f0d5e…), §5.1, p.23 (PDF p.25): "Let A be a level-i A-DST, and let A′ be any
subsequence of A. Then, for every threshold z, cross_z(A′) ≤ 4i². Consequently, if all elements of
A′ lie in an interval I, then cost(A′) = O(i²) · |I|."

**Formalization Note.** A level-`i` A-DST (`A.d = i`) has components `D_j` (`A.comp j`,
`1 ≤ j ≤ i`), each a hole-free section satisfying `Inv j` (`A₁` a sorted array); no ordering is
imposed between components. `A′` is any sublist of the value sequence of `A`. The cost bound is
stated with the explicit constant `4i²` that the crossing bound gives, for `I = [a, b]`,
`a ≤ b`. -/
theorem claim_22 (A : ADST Elt)
    (hA : ∀ j, 1 ≤ j → j ≤ A.d → Inv j (A.comp j) ∧ (A.comp j).holes = 0)
    (A' : List ℝ) (hsub : A'.Sublist A.vals) :
    (∀ z : ℝ, cross z A' ≤ 4 * A.d ^ 2) ∧
      ∀ a b : ℝ, a ≤ b → (∀ v ∈ A', a ≤ v ∧ v ≤ b) →
        cost A' ≤ 4 * (A.d : ℝ) ^ 2 * (b - a) := by sorry

end DynSort
