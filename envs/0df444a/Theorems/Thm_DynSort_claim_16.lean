-- Prove2me | Theorems.Thm_DynSort_claim_16
-- name    : DynSort.claim_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:38:05.457324+00:00
-- url     : https://prove2.me/theorems/4a705042-7420-479a-8dc1-7a916b011e13
-- title:
--   Claim 16 — SimpleStart2End moves the hole from the first to the last cell
-- statement:
--   Let $R$ be a level-$d$ root satisfying the structural invariants, with distinct elements and exactly one hole, and let $S$ be a section of $R$ of level $i$ whose first cell is the hole, where $S$ is not the last original section of a three-block parent. After SimpleStart2End $(i)$ on $S$:
--
--   1. $R$ satisfies all structural invariants and is a level-$d$ root;
--   2. $R$ has the same stored elements and exactly one hole;
--   3. the hole is the last cell of $S$.
--
--   **Formalization Note** The condition on $S$ is the applicability condition of SimpleStart2End (p.13): its address does not end at the index of a last original section.
--
--   Differences from the source:
--   - reading: Claim 16 for the DST on which SimpleStart2End is called → S is not the last original section of a three-block parent; reason: the operation "only applies when the DST is not the unique original section of a last block" (p.13); the proof uses it (p.50)
--   - encoding: a DST inside the tree on which the operation is called → the section at an address of a level-d root R satisfying the invariants, with at most 24·2^{d−1} cells, distinct elements and exactly one hole; reason: the operations reach into parent sections and ReBuild may replace sections, so they act on a root; the capacity holds for every DST and A-DST component (p.54)
--   - encoding: the hole reaches the last position of the DST → the hole is the cell with the absolute index of the section's last cell at entry; reason: ReBuild of an enclosing section can replace the section's object but never its interval
--   - encoding: elements are distinct reals (ties broken by infinitesimal perturbations, p.11) → elements of ℝ ×ₗ ℕ, a value and an identifier ordered lexicographically; reason: the identifier is the perturbation; every instance of the source is one of these
-- source:
--   Azar, Bhore, Dey, Panigrahi, Vardi, Zhang, Online and Fully-Dynamic Sorting, STOC 2027 submission (manuscript sha256 da7f0d5ef6191ccaa6c70faec62234592c6d108cd2357bda3e5b6dac010acf6c), Claim 16, p.17 (PDF p.19); proof pp.49–50 (PDF pp.51–52); p.13 (applicability)

import Mathlib
import Definitions.Def_DynSort_Inv
import Definitions.Def_DynSort_simpleStart2End

namespace DynSort

/-- **Claim 16**, Y. Azar, S. Bhore, D. Dey, D. Panigrahi, O. Vardi, I. Zhang, *Online and Fully-Dynamic Sorting*,
STOC 2027 submission (manuscript sha256 da7f0d5e…), §4.5.1, p.17 (PDF p.19; proof pp.49–50): "The SimpleStart2End operation
moves the hole from the first to the last position of the DST, while preserving all structural
invariants."

**Formalization Note.** Inside a level-`d` root `R` satisfying the invariants, with distinct
elements and exactly one hole, the section `S` at address `a` has level `i` and its first cell is
the hole. SimpleStart2End "only applies when the DST is not the unique original section of a last
block" (p.13): the address does not end in `3`, the index of `O₃` in a three-block parent. After
SimpleStart2End (i), `R` satisfies the invariants and the capacity, keeps its elements and its one
hole, and the hole is the last cell of `S`'s interval. -/
theorem claim_16 (d i : ℕ) (a : List ℕ) (R S : Sec Elt)
    (hR : RootInv d R) (hnd : R.stored.Nodup) (hholes : R.holes = 1)
    (hS : R.get a = some S) (hi : a.length + i = d) (hlast : a.getLast? ≠ some 3)
    (hhole : S.flat.head? = some none) :
    let st := simpleStart2End d i a ⟨R, {}⟩
    RootInv d st.root ∧ st.root.holes = 1 ∧ st.root.stored.Perm R.stored ∧
      st.root.flat[R.offset a + S.size - 1]? = some none := by sorry

end DynSort
