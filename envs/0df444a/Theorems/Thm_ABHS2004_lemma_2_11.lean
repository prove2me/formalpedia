-- Prove2me | Theorems.Thm_ABHS2004_lemma_2_11
-- name    : ABHS2004.lemma_2_11
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-30T01:57:41.66751+00:00
-- url     : https://prove2.me/theorems/c84a3ce3-0a4d-4f00-8a88-301a8a774ed9
-- title:
--   Lemma 2.11: Non-Size-Increasing Base Constants
-- statement:
--   Every base-level constant `c` (`0, S₀, S₁, par, +_⋄, if, destr, case`) is non-size-increasing: its value on arguments `w⃗` has size at most the sum of its linear (`0`-modal) arguments plus `1` when the leading argument is nonlinear (`!`).
-- source:
--   Klaus Aehlig, Ulrich Berger, Martin Hofmann, and Helmut Schwichtenberg, 'An arithmetic for non-size-increasing polynomial-time computation', Theoretical Computer Science 318(1-2), 2004, pp. 3-27 (doi:10.1016/j.tcs.2003.10.023). Lemma 2.11, p. 11.

import Definitions.Def_ABHS2004_TermSystem

namespace ABHS2004

theorem lemma_2_11 {r s : Term} {ρ : Ty}
    (ht : HasType r ρ) (hred : RedStep r s) :
    HasType s ρ ∧ ∀ v ∈ freeVarOccurrences s, v ∈ freeVarOccurrences r := by sorry

end ABHS2004
