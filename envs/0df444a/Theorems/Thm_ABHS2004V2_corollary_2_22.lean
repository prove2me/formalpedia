-- Prove2me | Theorems.Thm_ABHS2004V2_corollary_2_22
-- name    : ABHS2004V2.corollary_2_22
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-21T05:21:15.691959+00:00
-- url     : https://prove2.me/theorems/b330b39f-a07c-45f0-9ebf-89095ecd30e6
-- title:
--   Lemma 2.21 and Corollary 2.22 — Bound on reduction sequences
-- statement:
--   Each bounded reduction of a typed term strictly decreases $\vartheta$. The step count of a reduction sequence is at most the initial measure with parameter the number of free variables.
-- source:
--   Klaus Aehlig, Ulrich Berger, Martin Hofmann and Helmut Schwichtenberg (2004), An arithmetic for non-size-increasing polynomial-time computation, TCS 318, Lemma 2.21 and Corollary 2.22. https://www.mathematik.uni-muenchen.de/~schwicht/papers/abhs01/ICC-TCS/ansipt.pdf

import Definitions.Def_ABHS2004V2_TermSystem

namespace ABHS2004V2

/-- Lemma 2.21 and Corollary 2.22. A bounded reduction strictly decreases `theta`,
which bounds the length of a reduction sequence. -/
theorem corollary_2_22 {r : Term} {ρ : Ty} (ht : HasType r ρ) :
    (∀ (n : Nat) (r' : Term), RedStepBounded n r r' → theta n r' < theta n r) ∧
    (∀ (k : Nat) (r' : Term), RedSteps k r r' → k ≤ theta (freeVarCount r) r) := by sorry

end ABHS2004V2
