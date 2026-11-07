-- Prove2me | Theorems.Thm_DynSort_claim_20
-- name    : DynSort.claim_20
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:40:04.769246+00:00
-- url     : https://prove2.me/theorems/4d351101-c9e9-4e3a-a999-3be518b8301a
-- title:
--   Claim 20 — Any2End moves the hole from any cell to the last cell
-- statement:
--   Let $R_0$ be a level-$d$ root with no hole, satisfying the structural invariants and with distinct elements, let $S$ be a section of $R_0$ of level $i$, and let $e$ be an element of $S$. Remove $e$ from its cell, creating a hole, and apply Any2End $(i)$ to $S$. Then the result:
--
--   1. satisfies all structural invariants, except possibly that the middle original section of a three-block section of $R_0$ containing $S$ in its middle original section stores no element; it has at most $24\cdot2^{d-1}$ cells;
--   2. stores the elements of $R_0$ other than $e$, and has exactly one hole;
--   3. has the hole in the last cell of $S$.
--
--   When $S$ is a whole DST (as in Delete) there is no such enclosing section, and all invariants hold.
--
--   **Formalization Note** The state just after the deletion need not satisfy the invariants, since $e$ may have been the only element of a middle original section. The exception in 1 concerns a section outside the DST $S$; the caller repairs it.
--
--   Differences from the source:
--   - reading: Any2End preserves all structural invariants of the DST → all invariants of the root, except that a middle original section containing S may store no element; all invariants when S is the whole root; reason: the invariants preserved are those of the DST S (the proof's induction, p.52); if e was the only element of S and S fills a middle original section, that section of the enclosing DST is empty after any operation on S alone
--   - encoding: a hole at an arbitrary position → the hole created by deleting an element e of S from a hole-free root satisfying the invariants; reason: this is the input of Any2End in Delete (p.25), the only caller
--   - encoding: a DST inside the tree on which the operation is called → the section at an address of a level-d root R satisfying the invariants, with at most 24·2^{d−1} cells, distinct elements and exactly one hole; reason: the operations reach into parent sections and ReBuild may replace sections, so they act on a root; the capacity holds for every DST and A-DST component (p.54)
--   - encoding: the hole reaches the last position of the DST → the hole is the cell with the absolute index of the section's last cell at entry; reason: ReBuild of an enclosing section can replace the section's object but never its interval
--   - encoding: elements are distinct reals (ties broken by infinitesimal perturbations, p.11) → elements of ℝ ×ₗ ℕ, a value and an identifier ordered lexicographically; reason: the identifier is the perturbation; every instance of the source is one of these
-- source:
--   Azar, Bhore, Dey, Panigrahi, Vardi, Zhang, Online and Fully-Dynamic Sorting, STOC 2027 submission (manuscript sha256 da7f0d5ef6191ccaa6c70faec62234592c6d108cd2357bda3e5b6dac010acf6c), Claim 20, p.21 (PDF p.23); proof pp.52–53 (PDF pp.54–55)

import Mathlib
import Definitions.Def_DynSort_Inv
import Definitions.Def_DynSort_any2End

namespace DynSort

/-- **Claim 20**, Y. Azar, S. Bhore, D. Dey, D. Panigrahi, O. Vardi, I. Zhang, *Online and Fully-Dynamic Sorting*,
STOC 2027 submission (manuscript sha256 da7f0d5e…), §4.5.2, p.21 (PDF p.23; proof pp.52–53): "The Any2End operation moves
the hole from an arbitrary position to the last position of the DST, while preserving all
structural invariants."

**Formalization Note.** The hole is created by deleting an element `e` of the section `S` at
address `a` (level `i`) of a hole-free level-`d` root `R₀` satisfying the invariants, with
distinct elements (this is how Delete uses Any2End, p.25). The state after the deletion need not
satisfy the invariants: `e` may have been the only element of a middle original section. After
Any2End (i) the root satisfies the invariants and the capacity, except that a middle original
section containing `S` may now store no element (its three-block section is not part of the DST
`S`; it is repaired by the caller), stores the elements of `R₀` except `e`, has exactly one hole,
and the hole is the last cell of `S`'s interval. For a whole DST (`a = []`, as in Delete) there is
no such section, and the exit is `RootInv d`. -/
theorem claim_20 (d i : ℕ) (a : List ℕ) (R0 S : Sec Elt)
    (hR : RootInv d R0) (hnd : R0.stored.Nodup) (h0 : R0.holes = 0)
    (hS : R0.get a = some S) (hi : a.length + i = d) (e : Elt) (he : e ∈ S.stored) :
    let st := any2End d i a ⟨R0.eraseElt e, {}⟩
    InvLoose d st.root ∧ st.root.size ≤ 24 * 2 ^ (d - 1) ∧ st.root.holes = 1 ∧
      (∀ (b : List ℕ) (T : Sec Elt), st.root.get b = some T → ¬ (b ++ [2]) <+: a →
        midNonempty T) ∧
      st.root.stored.Perm (R0.stored.erase e) ∧
      st.root.flat[R0.offset a + S.size - 1]? = some none := by sorry

end DynSort
