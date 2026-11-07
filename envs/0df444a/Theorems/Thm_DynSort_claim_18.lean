-- Prove2me | Theorems.Thm_DynSort_claim_18
-- name    : DynSort.claim_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:38:26.922735+00:00
-- url     : https://prove2.me/theorems/ac502ac9-e238-4b0d-a442-866615b0ebce
-- title:
--   Claim 18 — Start2End moves the hole from the first to the last cell
-- statement:
--   Let $R$ be a level-$d$ root satisfying the structural invariants, with distinct elements and exactly one hole, and let $S$ be a section of $R$ of level $i$ whose first cell is the hole. After Start2End $(i)$ on $S$:
--
--   1. $R$ satisfies all structural invariants and is a level-$d$ root;
--   2. $R$ has the same stored elements and exactly one hole;
--   3. the hole is the last cell of $S$.
--
--   Delete uses Start2End to carry the hole through every component after the one where the deletion occurred.
--
--   Differences from the source:
--   - encoding: a DST inside the tree on which the operation is called → the section at an address of a level-d root R satisfying the invariants, with at most 24·2^{d−1} cells, distinct elements and exactly one hole; reason: the operations reach into parent sections and ReBuild may replace sections, so they act on a root; the capacity holds for every DST and A-DST component (p.54)
--   - encoding: the hole reaches the last position of the DST → the hole is the cell with the absolute index of the section's last cell at entry; reason: ReBuild of an enclosing section can replace the section's object but never its interval
--   - encoding: elements are distinct reals (ties broken by infinitesimal perturbations, p.11) → elements of ℝ ×ₗ ℕ, a value and an identifier ordered lexicographically; reason: the identifier is the perturbation; every instance of the source is one of these
-- source:
--   Azar, Bhore, Dey, Panigrahi, Vardi, Zhang, Online and Fully-Dynamic Sorting, STOC 2027 submission (manuscript sha256 da7f0d5ef6191ccaa6c70faec62234592c6d108cd2357bda3e5b6dac010acf6c), Claim 18, p.19 (PDF p.21); proof pp.50–51 (PDF pp.52–53)

import Mathlib
import Definitions.Def_DynSort_Inv
import Definitions.Def_DynSort_start2End

namespace DynSort

/-- **Claim 18**, Y. Azar, S. Bhore, D. Dey, D. Panigrahi, O. Vardi, I. Zhang, *Online and Fully-Dynamic Sorting*,
STOC 2027 submission (manuscript sha256 da7f0d5e…), §4.5.2, p.19 (PDF p.21; proof pp.50–51): "The Start2End operation moves
the hole from the first to the last position of the DST, while preserving all structural
invariants."

**Formalization Note.** Inside a level-`d` root `R` satisfying the invariants, with distinct
elements and exactly one hole, the section `S` at address `a` has level `i` and its first cell is
the hole. After Start2End (i), `R` satisfies the invariants and the capacity, keeps its elements
and its one hole, and the hole is the last cell of `S`'s interval. -/
theorem claim_18 (d i : ℕ) (a : List ℕ) (R S : Sec Elt)
    (hR : RootInv d R) (hnd : R.stored.Nodup) (hholes : R.holes = 1)
    (hS : R.get a = some S) (hi : a.length + i = d) (hhole : S.flat.head? = some none) :
    let st := start2End d i a ⟨R, {}⟩
    RootInv d st.root ∧ st.root.holes = 1 ∧ st.root.stored.Perm R.stored ∧
      st.root.flat[R.offset a + S.size - 1]? = some none := by sorry

end DynSort
