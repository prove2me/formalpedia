-- Prove2me | Theorems.Thm_DynSort_claim_19
-- name    : DynSort.claim_19
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:38:28.341686+00:00
-- url     : https://prove2.me/theorems/7145cf99-38d5-4676-adbb-dcbe7ef9c40b
-- title:
--   Claim 19 — Start2End $(i)$ makes $O(i^2)$ moves excluding ReBuild
-- statement:
--   There is a constant $C$ such that for every root level $d$, every level $i$ and every input of Start2End $(i)$ as in Claim 18, the number of element movements made by Start2End $(i)$, excluding those of ReBuild, is at most
--   $$C\,i^2 .$$
--
--   **Formalization Note** The movements counted are those of InsertMax (one each) and of the level-$1$ shifts (one per shifted element).
--
--   Differences from the source:
--   - encoding: O(i²) recourse → ∃ C : ℕ, before every other quantifier, with moves ≤ C·i² for every input; reason: the constant of O(·) is absolute
--   - encoding: a DST inside the tree on which the operation is called → the section at an address of a level-d root R satisfying the invariants, with at most 24·2^{d−1} cells, distinct elements and exactly one hole; reason: the operations reach into parent sections and ReBuild may replace sections, so they act on a root; the capacity holds for every DST and A-DST component (p.54)
--   - encoding: elements are distinct reals (ties broken by infinitesimal perturbations, p.11) → elements of ℝ ×ₗ ℕ, a value and an identifier ordered lexicographically; reason: the identifier is the perturbation; every instance of the source is one of these
-- source:
--   Azar, Bhore, Dey, Panigrahi, Vardi, Zhang, Online and Fully-Dynamic Sorting, STOC 2027 submission (manuscript sha256 da7f0d5ef6191ccaa6c70faec62234592c6d108cd2357bda3e5b6dac010acf6c), Claim 19, p.19 (PDF p.21); proof pp.19–20 (PDF pp.21–22)

import Mathlib
import Definitions.Def_DynSort_Inv
import Definitions.Def_DynSort_start2End

namespace DynSort

/-- **Claim 19**, Y. Azar, S. Bhore, D. Dey, D. Panigrahi, O. Vardi, I. Zhang, *Online and Fully-Dynamic Sorting*,
STOC 2027 submission (manuscript sha256 da7f0d5e…), §4.5.2, p.19 (PDF p.21; proof pp.19–20): "Excluding recourse incurred by
any ReBuild calls, Start2End (i) incurs O(i²) recourse."

**Formalization Note.** One constant `C` serves every root level `d`, every level `i` and every
input of Start2End as in Claim 18. `moves` counts the element movements of InsertMax (one each)
and of the level-1 shifts (one per shifted element), and excludes ReBuild. -/
theorem claim_19 :
    ∃ C : ℕ, ∀ (d i : ℕ) (a : List ℕ) (R S : Sec Elt),
      RootInv d R → R.stored.Nodup → R.holes = 1 → R.get a = some S → a.length + i = d →
      S.flat.head? = some none →
      (start2End d i a ⟨R, {}⟩).ctr.moves ≤ C * i ^ 2 := by sorry

end DynSort
