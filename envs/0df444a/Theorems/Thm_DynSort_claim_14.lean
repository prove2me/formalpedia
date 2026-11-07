-- Prove2me | Theorems.Thm_DynSort_claim_14
-- name    : DynSort.claim_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:36:58.399087+00:00
-- url     : https://prove2.me/theorems/aa85d4f7-4188-4f97-8e06-52f7f040ac4c
-- title:
--   Claim 14 — JumpDown preserves the invariants and moves the hole to the end
-- statement:
--   Let $R$ be a level-$d$ root satisfying the structural invariants, with distinct elements and exactly one hole. Let $S=O_1\mid T_2O_2\mid O_3$ be a three-block section of $R$ of level $i$ whose transfer section $T_2$ ends with the hole. After JumpDown $(i)$ on $S$:
--
--   1. $R$ satisfies all structural invariants and is a level-$d$ root;
--   2. $R$ has the same stored elements and exactly one hole;
--   3. the hole is the last cell of $S$.
--
--   JumpDown is the step that carries a hole through the last blocks at every level; Claims 16, 18 and 20 call it.
--
--   Differences from the source:
--   - encoding: a DST inside the tree on which the operation is called → the section at an address of a level-d root R satisfying the invariants, with at most 24·2^{d−1} cells, distinct elements and exactly one hole; reason: the operations reach into parent sections and ReBuild may replace sections, so they act on a root; the capacity holds for every DST and A-DST component (p.54)
--   - encoding: the hole reaches the last position of the DST → the hole is the cell with the absolute index of the section's last cell at entry; reason: ReBuild of an enclosing section can replace the section's object but never its interval
--   - encoding: elements are distinct reals (ties broken by infinitesimal perturbations, p.11) → elements of ℝ ×ₗ ℕ, a value and an identifier ordered lexicographically; reason: the identifier is the perturbation; every instance of the source is one of these
-- source:
--   Azar, Bhore, Dey, Panigrahi, Vardi, Zhang, Online and Fully-Dynamic Sorting, STOC 2027 submission (manuscript sha256 da7f0d5ef6191ccaa6c70faec62234592c6d108cd2357bda3e5b6dac010acf6c), Claim 14, p.16 (PDF p.18); proof pp.48–49 (PDF pp.50–51)

import Mathlib
import Definitions.Def_DynSort_Inv
import Definitions.Def_DynSort_jumpDown

namespace DynSort

/-- **Claim 14**, Y. Azar, S. Bhore, D. Dey, D. Panigrahi, O. Vardi, I. Zhang, *Online and Fully-Dynamic Sorting*,
STOC 2027 submission (manuscript sha256 da7f0d5e…), §4.5.1, p.16 (PDF p.18; proof pp.48–49): "The JumpDown operation
preserves all structural invariants and moves the hole to the last position of the DST."

**Formalization Note.** Inside a level-`d` root `R` satisfying the invariants, with distinct
elements and exactly one hole, the section at address `a` has level `i` (`a.length + i = d`) and
three blocks `O₁ | T₂ O₂ | O₃`, and the hole is the last cell of `T₂` (the input of JumpDown,
p.16). After JumpDown (i), `R` satisfies the invariants and the capacity, keeps its elements and
its one hole, and the hole is the last cell of the section's interval. -/
theorem claim_14 (d i : ℕ) (a : List ℕ) (R O1 T2 O2 O3 : Sec Elt)
    (hR : RootInv d R) (hnd : R.stored.Nodup) (hholes : R.holes = 1)
    (hS : R.get a = some (.three O1 T2 O2 O3)) (hi : a.length + i = d)
    (hhole : T2.flat.getLast? = some none) :
    let st := jumpDown d i a ⟨R, {}⟩
    RootInv d st.root ∧ st.root.holes = 1 ∧ st.root.stored.Perm R.stored ∧
      st.root.flat[R.offset a + (Sec.three O1 T2 O2 O3).size - 1]? = some none := by sorry

end DynSort
