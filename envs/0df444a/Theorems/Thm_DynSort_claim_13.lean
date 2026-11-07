-- Prove2me | Theorems.Thm_DynSort_claim_13
-- name    : DynSort.claim_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:35:39.282197+00:00
-- url     : https://prove2.me/theorems/878cedab-4c8e-405d-a65e-bc282d872148
-- title:
--   Claim 13 — SwapHole $(O_2,T_2)$ maintains all structural invariants
-- statement:
--   Let $R$ be a level-$d$ root with distinct elements, at most $24\cdot2^{d-1}$ cells and exactly one hole, and let $S=O_1\mid T_2O_2\mid O_3$ be a three-block section of $R$ whose middle original section $O_2$ has the hole as its first cell. Suppose $R$ satisfies all structural invariants, except that $O_2$ of $S$ itself may store no element. Apply SwapHole $(O_2,T_2)$, including its repair step. Then the result:
--
--   1. satisfies all structural invariants, and is a level-$d$ root;
--   2. has the same stored elements and exactly one hole;
--   3. has the hole in the same absolute cell (now the last cell of $T_2$), or in the last cell of $S$ or of a section enclosing $S$, when ReBuild has moved it there.
--
--   This is the state in which every hole-routing operation calls SwapHole, right after InsertMax has taken $\min O_2$.
--
--   **Formalization Note** Cells are compared by absolute index in $R$, and "the last cell of a section enclosing $S$" refers to that section's interval before the operation.
--
--   Differences from the source:
--   - reading: SwapHole maintains all structural invariants (the state on entry is not specified) → entry: all invariants except that the middle original section O₂ of S may store no element, the hole first in O₂; exit: all invariants; reason: this is the state of every SwapHole call of §4.5; O₂ may have just lost its last element to InsertMax, which is the repair case of p.15
--   - reading: SwapHole (D, D′) for any adjacent DSTs, in either direction → SwapHole (O₂, T₂) from right to left between the original and transfer sections of a middle block of a section S of R; reason: inside a DST the transfer "occurs between the transfer and original sections of a middle block" (p.15), and every call in §4.5 is SwapHole (O₂, T₂) from right to left; the transfer between A-DST components is Claim 25 (p.25), not this claim
--   - generalization: maintains all structural invariants → also: same stored elements, one hole, and the hole on the transferred cell or at the end of S or of an enclosing section; reason: these are what the callers use (pp.48–53); dropping them gives the source's claim
--   - encoding: a DST inside the tree on which the operation is called → the section at an address of a level-d root R satisfying the invariants, with at most 24·2^{d−1} cells, distinct elements and exactly one hole; reason: the operations reach into parent sections and ReBuild may replace sections, so they act on a root; the capacity holds for every DST and A-DST component (p.54)
--   - encoding: elements are distinct reals (ties broken by infinitesimal perturbations, p.11) → elements of ℝ ×ₗ ℕ, a value and an identifier ordered lexicographically; reason: the identifier is the perturbation; every instance of the source is one of these
-- source:
--   Azar, Bhore, Dey, Panigrahi, Vardi, Zhang, Online and Fully-Dynamic Sorting, STOC 2027 submission (manuscript sha256 da7f0d5ef6191ccaa6c70faec62234592c6d108cd2357bda3e5b6dac010acf6c), Claim 13, p.15 (PDF p.17); proof pp.47–48 (PDF pp.49–50)

import Mathlib
import Definitions.Def_DynSort_Inv
import Definitions.Def_DynSort_swapHole

namespace DynSort

/-- **Claim 13**, Y. Azar, S. Bhore, D. Dey, D. Panigrahi, O. Vardi, I. Zhang, *Online and Fully-Dynamic Sorting*,
STOC 2027 submission (manuscript sha256 da7f0d5e…), §4.4, p.15 (PDF p.17; proof pp.47–48): "The SwapHole operation maintains
all structural invariants of the DSTs."

**Formalization Note.** Inside a level-`d` root `R`, `S = O₁ | T₂ O₂ | O₃` is the three-block
section at address `a`, and the unique hole is the first cell of `O₂`; this is the state in which
every operation of §4.5 calls SwapHole (O₂, T₂), just after InsertMax took `min O₂`. So `R`
satisfies every invariant, except that `O₂` of `S` itself may have lost its last element. After
SwapHole (O₂, T₂) with its repair step, `R` satisfies all invariants and the capacity, keeps its
elements and its one hole, and the hole is the same absolute cell (now the last cell of `T₂`), or
the last cell (in `R`'s original layout) of `S` or of a section enclosing it, when ReBuild moved it
there. -/
theorem claim_13 (d : ℕ) (a : List ℕ) (R O1 T2 O2 O3 : Sec Elt)
    (hloose : InvLoose d R) (hcap : R.size ≤ 24 * 2 ^ (d - 1)) (hnd : R.stored.Nodup)
    (hholes : R.holes = 1) (hS : R.get a = some (.three O1 T2 O2 O3))
    (hhole : O2.flat.head? = some none)
    (hmid : ∀ (b : List ℕ) (T : Sec Elt), R.get b = some T → b ≠ a → midNonempty T) :
    let st := swapHole d (a ++ [2]) (a ++ [1]) ⟨R, {}⟩
    RootInv d st.root ∧ st.root.holes = 1 ∧ st.root.stored.Perm R.stored ∧
      (st.root.flat[R.offset (a ++ [2])]? = some none ∨
        ∃ (p : List ℕ) (P : Sec Elt), p <+: a ∧ R.get p = some P ∧
          st.root.flat[R.offset p + P.size - 1]? = some none) := by sorry

end DynSort
