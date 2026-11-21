-- Prove2me | Theorems.Thm_ABHS2004V2_lemma_2_11
-- name    : ABHS2004V2.lemma_2_11
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-21T05:20:48.303187+00:00
-- url     : https://prove2.me/theorems/29999186-28de-4ca2-88fa-949a6c4b9ad1
-- title:
--   Lemma 2.11 — Type and free-variable preservation
-- statement:
--   One-step reduction of an affinely typed term preserves the type and introduces no new free variables.
-- source:
--   Klaus Aehlig, Ulrich Berger, Martin Hofmann and Helmut Schwichtenberg (2004), An arithmetic for non-size-increasing polynomial-time computation, TCS 318, Lemma 2.11. https://www.mathematik.uni-muenchen.de/~schwicht/papers/abhs01/ICC-TCS/ansipt.pdf

import Definitions.Def_ABHS2004V2_TermSystem

namespace ABHS2004V2

/-- Lemma 2.11. One-step reduction preserves the program's type and introduces no
new free variables. -/
theorem lemma_2_11 {r s : Term} {ρ : Ty}
    (ht : HasType r ρ) (hred : RedStep r s) :
    HasType s ρ ∧ ∀ v ∈ freeVarOccurrences s, v ∈ freeVarOccurrences r := by sorry

end ABHS2004V2
