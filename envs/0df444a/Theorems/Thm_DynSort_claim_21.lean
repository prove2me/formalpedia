-- Prove2me | Theorems.Thm_DynSort_claim_21
-- name    : DynSort.claim_21
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:39:48.898491+00:00
-- url     : https://prove2.me/theorems/48a37563-d45e-4f7d-96c4-6adf2232982f
-- title:
--   Claim 21 — Any2End $(i)$ makes $O(i^3)$ moves excluding ReBuild
-- statement:
--   There is a constant $C$ such that for every root level $d$, every level $i$ and every input of Any2End $(i)$ as in Claim 20, the number of element movements made by Any2End $(i)$, excluding those of ReBuild, is at most
--   $$C\,i^3 .$$
--
--   Differences from the source:
--   - encoding: O(i³) recourse → ∃ C : ℕ, before every other quantifier, with moves ≤ C·i³ for every input; reason: the constant of O(·) is absolute
--   - encoding: a DST inside the tree on which the operation is called → the section at an address of a level-d root R satisfying the invariants, with at most 24·2^{d−1} cells, distinct elements and exactly one hole; reason: the operations reach into parent sections and ReBuild may replace sections, so they act on a root; the capacity holds for every DST and A-DST component (p.54)
--   - encoding: elements are distinct reals (ties broken by infinitesimal perturbations, p.11) → elements of ℝ ×ₗ ℕ, a value and an identifier ordered lexicographically; reason: the identifier is the perturbation; every instance of the source is one of these
-- source:
--   Azar, Bhore, Dey, Panigrahi, Vardi, Zhang, Online and Fully-Dynamic Sorting, STOC 2027 submission (manuscript sha256 da7f0d5ef6191ccaa6c70faec62234592c6d108cd2357bda3e5b6dac010acf6c), Claim 21, p.21 (PDF p.23); proof pp.21–22 (PDF pp.23–24)

import Mathlib
import Definitions.Def_DynSort_Inv
import Definitions.Def_DynSort_any2End

namespace DynSort

/-- **Claim 21**, Y. Azar, S. Bhore, D. Dey, D. Panigrahi, O. Vardi, I. Zhang, *Online and Fully-Dynamic Sorting*,
STOC 2027 submission (manuscript sha256 da7f0d5e…), §4.5.2, p.21 (PDF p.23; proof pp.21–22): "Excluding recourse incurred by
any ReBuild calls, Any2End (i) incurs O(i³) recourse."

**Formalization Note.** One constant `C` serves every root level `d`, every level `i` and every
input of Any2End as in Claim 20. `moves` excludes ReBuild. -/
theorem claim_21 :
    ∃ C : ℕ, ∀ (d i : ℕ) (a : List ℕ) (R0 S : Sec Elt) (e : Elt),
      RootInv d R0 → R0.stored.Nodup → R0.holes = 0 → R0.get a = some S → a.length + i = d →
      e ∈ S.stored →
      (any2End d i a ⟨R0.eraseElt e, {}⟩).ctr.moves ≤ C * i ^ 3 := by sorry

end DynSort
