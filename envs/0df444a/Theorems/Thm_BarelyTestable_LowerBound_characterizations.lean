-- Prove2me | Theorems.Thm_BarelyTestable_LowerBound_characterizations
-- name    : BarelyTestable.LowerBound.characterizations
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:21:16.373246+00:00
-- url     : https://prove2.me/theorems/ee9d3187-1bce-46b8-ac58-5fff50ec63f2
-- title:
--   Lemma 2.2 — three characterizations of submodularity
-- statement:
--   For every real function $f$ on the $n$-dimensional Boolean cube, the following three conditions are equivalent: the lattice submodularity inequality, nonnegative slack on every valid coordinate square, and diminishing returns on comparable vertices. Explicitly,
--
--   $$\mathrm{Submodular}(f)\iff\text{every square has nonnegative slack}\iff\forall S\subseteq T,\ u\notin T:\ f(T\cup\{u\})-f(T)\le f(S\cup\{u\})-f(S).$$
--
--   Both equivalences are included, also for zero- and one-dimensional cubes. This connects the reused unrestricted lattice definition to the local square tests.
--
--   Differences from the source:
--   - encoding: Boolean vectors with coordinates numbered from 1 → finite subsets of Fin n, numbered from 0; reason: the incidence-vector bijection preserves every vertex, union, intersection and coordinate square
-- source:
--   Diptaksho Palit, Yuichi Yoshida, STOC 2027 submission #722 (October 2026), Lemma 2.2, p. 9 (printed = PDF page); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/722.pdf; PDF SHA256 a095e6ef801edf5b0ce3967efca977e04b7a0b4374e874116509d73837bd14f3

import Mathlib
import Definitions.Def_BarelyTestable_LowerBound_Cube

set_option autoImplicit false

namespace BarelyTestable.LowerBound

open NonmonotoneSubmod.Shared MeasureTheory

/-- Lemma 2.2, p.9: all three conditions, with both equivalences. -/
theorem characterizations {n : ℕ} (f : Oracle (Fin n)) :
    (Submodular f ↔ NonnegativeSquares f) ∧
    (Submodular f ↔ DiminishingReturns f) := by sorry

end BarelyTestable.LowerBound
