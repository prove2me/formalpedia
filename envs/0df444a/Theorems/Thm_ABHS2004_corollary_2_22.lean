-- Prove2me | Theorems.Thm_ABHS2004_corollary_2_22
-- name    : ABHS2004.corollary_2_22
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-30T01:58:00.308589+00:00
-- url     : https://prove2.me/theorems/9332b2a2-fce3-4dee-ba84-816298c4e419
-- title:
--   Corollary 2.22: Polynomial Step and Space Bounds for Closed Terms
-- statement:
--   For every well-typed closed term `M : ρ` of the `!`-free affine term system, its normal form is computable in `|M|^{2^{d+1}}` steps with intermediate terms of size at most `|M|^{2^d}`, where `d` is the nesting depth of `it` in `M`.
-- source:
--   Klaus Aehlig, Ulrich Berger, Martin Hofmann, and Helmut Schwichtenberg, 'An arithmetic for non-size-increasing polynomial-time computation', Theoretical Computer Science 318(1-2), 2004, pp. 3-27 (doi:10.1016/j.tcs.2003.10.023). Corollary 2.22, p. 14.

import Definitions.Def_ABHS2004_TermSystem

namespace ABHS2004

theorem corollary_2_22 {r : Term} {ρ : Ty} (ht : HasType r ρ) :
    (∀ (n : Nat) (r' : Term), RedStepBounded n r r' → theta n r' < theta n r) ∧
    (∀ (k : Nat) (r' : Term), RedSteps k r r' → k ≤ theta (freeVarCount r) r) := by sorry

end ABHS2004
