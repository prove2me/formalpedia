-- Prove2me | Theorems.Thm_DynSort_claim_11
-- name    : DynSort.claim_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:34:32.803403+00:00
-- url     : https://prove2.me/theorems/62ff2219-f7d7-438b-bb88-877e80c3cf01
-- title:
--   Claim 11 — ReBuild restores all structural invariants
-- statement:
--   Let $i\ge1$ and let $S$ be any level-$i$ section, not necessarily satisfying the invariants, with at most one hole, distinct elements and at most $24\cdot2^{i-1}$ cells. Let $S'$ be the result of ReBuild. Then:
--
--   1. $S'$ satisfies all structural invariants of a level-$i$ DST, and is a level-$i$ root (at most one hole, at most $24\cdot2^{i-1}$ cells);
--   2. $S'$ has the same number of cells and the same stored elements as $S$;
--   3. if $S$ has a hole, it is the last cell of $S'$;
--   4. every transfer section of $S'$ is empty.
--
--   ReBuild is how SwapHole repairs violations, so every correctness claim of the hole-routing operations rests on this one.
--
--   **Formalization Note** The capacity $24\cdot2^{i-1}$ is the paper's own (p.54: "the rebuilding rule constructs a valid level-i DST from any collection of at most $24\cdot2^{i-1}$ cells").
--
--   Differences from the source:
--   - generalization: a DST requiring rebuilding inside a DST, so |D| ≤ 24·2^{i−1} − 1 at level i (p.46) → any section with at most 24·2^{i−1} cells, at most one hole and distinct elements, whatever its shape; reason: the rule needs only |D| ≤ 25·2^{i−1} − 2 (p.46); every section the paper rebuilds is such a section
--   - generalization: maintains all structural invariants → the invariants, plus: same cells, same stored elements, the hole last, all transfer sections empty, at most 24·2^{i−1} cells; reason: these are the properties of ReBuild stated on p.14; dropping them gives the source's claim
--   - encoding: elements are distinct reals (ties broken by infinitesimal perturbations, p.11) → elements of ℝ ×ₗ ℕ, a value and an identifier ordered lexicographically; reason: the identifier is the perturbation; every instance of the source is one of these
-- source:
--   Azar, Bhore, Dey, Panigrahi, Vardi, Zhang, Online and Fully-Dynamic Sorting, STOC 2027 submission (manuscript sha256 da7f0d5ef6191ccaa6c70faec62234592c6d108cd2357bda3e5b6dac010acf6c), Claim 11, p.14 (PDF p.16); proof pp.46–47 (PDF pp.48–49); capacity p.54 (PDF p.56)

import Mathlib
import Definitions.Def_DynSort_Inv
import Definitions.Def_DynSort_rebuild

namespace DynSort

/-- **Claim 11**, Y. Azar, S. Bhore, D. Dey, D. Panigrahi, O. Vardi, I. Zhang, *Online and Fully-Dynamic Sorting*,
STOC 2027 submission (manuscript sha256 da7f0d5e…), §4.4, p.14 (PDF p.16; proof pp.46–47): "The ReBuild operation maintains
all structural invariants of the DST."

**Formalization Note.** ReBuild applies to any level-`i` section `S` (`i ≥ 1`), including one
violating the invariants (that is what it repairs), with at most one hole, distinct elements, and
at most `24·2^{i−1}` cells, the capacity under which "the rebuilding rule constructs a valid
level-i DST" (p.54). The rebuilt section satisfies the invariants and the capacity, has the same
cells and stored elements, holds the hole (if any) in its last cell, and has all transfer sections
empty (p.14). -/
theorem claim_11 (i : ℕ) (hi : 1 ≤ i) (S : Sec Elt) (hcap : S.size ≤ 24 * 2 ^ (i - 1))
    (hh : S.holes ≤ 1) (hnd : S.stored.Nodup) :
    let S' := (rebuildSec i false S).1
    RootInv i S' ∧ S'.size = S.size ∧ S'.stored.Perm S.stored ∧
      (S.holes = 1 → S'.flat.getLast? = some none) ∧
      ∀ (b : List ℕ) (O1 T2 O2 O3 : Sec Elt),
        S'.get b = some (.three O1 T2 O2 O3) → T2.size = 0 := by sorry

end DynSort
