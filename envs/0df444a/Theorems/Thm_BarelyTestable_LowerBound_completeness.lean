-- Prove2me | Theorems.Thm_BarelyTestable_LowerBound_completeness
-- name    : BarelyTestable.LowerBound.completeness
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:22:16.928251+00:00
-- url     : https://prove2.me/theorems/12887db1-529a-4762-9494-08062760b0c2
-- title:
--   Proposition 3.3 — pointwise completeness
-- statement:
--   For every $m\ge9$ and every realization of all independent labels and shared table entries,
--
--   $$F^{(+1)}\text{ is submodular}.$$
--
--   Completeness holds for each hard function individually, rather than only with high probability. It supplies the YES support condition for the testing lower bound.
--
--   Differences from the source:
--   - encoding: two action bits and two halves with m blocks of m coordinates → Coord m = Bool ⊕ ((Fin m × Fin m) ⊕ (Fin m × Fin m)); reason: this coordinate type has 2m²+2 elements and coordEquiv explicitly renames it to Fin (2m²+2)
--   - reading: large enough m → m ≥ 9; reason: §3.2.1 p.16 proves Lemma 3.2 for every m ≥ 9, uniformly over all realizations and both signs
--   - encoding: F^(+1) → hard r true; reason: the Boolean true selects σ = +1 (YES)
-- source:
--   Diptaksho Palit, Yuichi Yoshida, STOC 2027 submission #722 (October 2026), Proposition 3.3, p. 13 (printed = PDF page); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/722.pdf; PDF SHA256 a095e6ef801edf5b0ce3967efca977e04b7a0b4374e874116509d73837bd14f3

import Mathlib
import Definitions.Def_BarelyTestable_LowerBound_Construction

set_option autoImplicit false

namespace BarelyTestable.LowerBound

open NonmonotoneSubmod.Shared MeasureTheory

/-- Proposition 3.3, p.13, pointwise for every realization. -/
theorem completeness {m : ℕ} (hm : 9 ≤ m) (r : Sample m) :
    Submodular (hard r true) := by sorry

end BarelyTestable.LowerBound
