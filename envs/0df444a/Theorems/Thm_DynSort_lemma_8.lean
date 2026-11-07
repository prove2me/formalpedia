-- Prove2me | Theorems.Thm_DynSort_lemma_8
-- name    : DynSort.lemma_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:34:48.282394+00:00
-- url     : https://prove2.me/theorems/ce0f662f-0c03-4168-bace-70509ba3022f
-- title:
--   Lemma 8 — $\mathrm{cross}_z(S)\le 4i$ and $\mathrm{cost}(S)\le 4i\,|I|$ for a level-$i$ DST
-- statement:
--   Let $S$ be a level-$i$ DST with no hole, and let $(x_1,\dots,x_k)$ be the values of its elements from left to right. Then for every threshold $z$,
--   $$\mathrm{cross}_z(x_1,\dots,x_k)\le 4i,$$
--   and if all values lie in an interval $I=[a,b]$ with $a\le b$, then
--   $$\mathrm{cost}(x_1,\dots,x_k)\le 4i\,(b-a).$$
--
--   This is the cost guarantee of a single DST; the A-DST bound of Claim 22 adds the components.
--
--   **Formalization Note** The invariants order elements (value, identifier) lexicographically, while crossings count values; a value threshold is a cut of that order.
--
--   Differences from the source:
--   - encoding: S an i-level DST, elements in an interval I, |I| → a hole-free section satisfying the level-i invariants, crossings and cost of its value sequence, I = [a, b] with a ≤ b and |I| = b − a; reason: a DST has no hole between operations; with a > b no interval contains the elements
--   - encoding: elements are distinct reals (ties broken by infinitesimal perturbations, p.11) → elements of ℝ ×ₗ ℕ, a value and an identifier ordered lexicographically; reason: the identifier is the perturbation; every instance of the source is one of these
-- source:
--   Azar, Bhore, Dey, Panigrahi, Vardi, Zhang, Online and Fully-Dynamic Sorting, STOC 2027 submission (manuscript sha256 da7f0d5ef6191ccaa6c70faec62234592c6d108cd2357bda3e5b6dac010acf6c), Lemma 8, p.12 (PDF p.14); proof p.45 (PDF p.47)

import Mathlib
import Definitions.Def_DynSort_cost
import Definitions.Def_DynSort_cross
import Definitions.Def_DynSort_Inv

namespace DynSort

/-- **Lemma 8**, Y. Azar, S. Bhore, D. Dey, D. Panigrahi, O. Vardi, I. Zhang, *Online and Fully-Dynamic Sorting*,
STOC 2027 submission (manuscript sha256 da7f0d5e…), §4.2, p.12 (PDF p.14; proof p.45): "Let S be an i-level DST. Then, for
every threshold z, we have cross_z(S) ≤ 4i. Consequently, if all elements of S lie in an interval
I, then we have cost(S) ≤ 4i · |I|."

**Formalization Note.** `S` is a hole-free section of `Elt`s satisfying `Inv i`; crossings and
cost are those of its value sequence `S.vals`, left to right. The interval is `I = [a, b]` with
`a ≤ b`, so `|I| = b − a`. -/
theorem lemma_8 (i : ℕ) (S : Sec Elt) (hS : Inv i S) (h0 : S.holes = 0) :
    (∀ z : ℝ, cross z S.vals ≤ 4 * i) ∧
      ∀ a b : ℝ, a ≤ b → (∀ v ∈ S.vals, a ≤ v ∧ v ≤ b) →
        cost S.vals ≤ 4 * i * (b - a) := by sorry

end DynSort
