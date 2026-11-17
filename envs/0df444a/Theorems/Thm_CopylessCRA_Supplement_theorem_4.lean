-- Prove2me | Theorems.Thm_CopylessCRA_Supplement_theorem_4
-- name    : CopylessCRA.Supplement.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T02:59:21.025369+00:00
-- url     : https://prove2.me/theorems/c8e46ac4-01ed-4b35-bbde-fc10771d3c95
-- title:
--   Theorem 4 — exact algorithms for the invertible and unipotent sectors
-- statement:
--   There are uniform exact Turing algorithms with the following guarantees for binary-encoded rational weighted representations.
--
--   1. A minimal representation can be computed in polynomial bit time, and invertibility can be decided in polynomial bit time.
--   2. For an invertible rational series, CCRA-computability is decidable.
--   3. Unipotence of a rational series is decidable in polynomial bit time.
--   4. For a unipotent rational series, CCRA-computability is decidable in polynomial bit time.
--
--   No polynomial-time bound is asserted for the general invertible-sector CCRA membership test.
--
--   This packages the paper's effective characterization while retaining the distinction between decidability and polynomial bit complexity.
--
--   Differences from the source:
--   - encoding: the source specifies binary-encoded rational entries, exact rational arithmetic and the Turing model in its proof → Lean gives a self-delimiting binary format and uses Mathlib's finite multi-tape Turing computability and polynomial-step predicates; reason: this is an explicit realization of the same bit-complexity model and does not assign unit cost to field operations
-- source:
--   Zeng–Cao–Dai–Wang–Ding, Copyless Cost Register Automata and Algebraic Groups, STOC 2027 submission (manuscript sha256 434d3094df2665371c402d5b5291b3c7f3a27a0d79384e4a8ec3ca3a46a92543), Theorem 4, p.3 (PDF p.5); Appendix C.1–C.2, pp.16–17 (PDF pp.18–19)

import Mathlib
import Definitions.Def_CopylessCRA_Supplement_WeightedRep

namespace CopylessCRA
namespace Supplement

/-- Zeng--Cao--Dai--Wang--Ding, *Copyless Cost Register Automata and Algebraic Groups*, STOC
2027 submission (manuscript sha256 434d3094...), Theorem 4, p.3 (PDF p.5), with the exact
complexity model fixed in Appendix C, pp.16--17 (PDF pp.18--19).

There are uniform Turing algorithms which (i) compute a minimal representation and decide
invertibility in polynomial bit time, (ii) decide CCRA-computability for invertible series, with no
polynomial-time claim, (iii) decide unipotence in polynomial bit time, and (iv) decide
CCRA-computability for unipotent series in polynomial bit time.

**Formalization Note** Inputs explicitly encode the alphabet size, dimension, and every rational
entry in binary.  Mathlib's `TM2ComputableInPolyTime` bounds a finite Turing machine by a natural
polynomial in that bitstring length, so rational arithmetic is not treated as unit cost.  The
general invertible-sector CCRA test intentionally has only `TM2Computable`. -/
theorem theorem_4 : exists A : DecisionAlgorithms, A.Correct := by sorry

end Supplement
end CopylessCRA
